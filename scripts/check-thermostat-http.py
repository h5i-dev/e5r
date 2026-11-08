#!/usr/bin/env python3
"""Check raw HTTP/decoder/auth boundaries on the pinned ELF (Apache-2.0).

Each case gets a fresh emulated UART, including early-rejection prefixes whose
remaining bytes need not form another request. This is an integration oracle,
not an ELF proof or a claim about physical connection framing.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
RV = ROOT / 'verification/rv32'
KEY = b'Authorization: Bearer dev-key\r\n'
INITIAL = (b'{"setpoint_dc":200,"temp_dc":200,"heater":false,'
           b'"relays":[false,false,false,false],"mode":"off"}')


def request(method=b'GET', path=b'/state', body=b'', extra=b'', auth=False,
            host=b'Host: thermostat\r\n', framing=None, version=b'1.1'):
    if framing is None:
        framing = b'Content-Length: ' + str(len(body)).encode() + b'\r\n'
    return (method + b' ' + path + b' HTTP/' + version + b'\r\n' + host + framing +
            (KEY if auth else b'') + extra + b'\r\n' + body)


def cases():
    normal = request()
    yield 'exact-initial-json', normal, 200, {}, INITIAL, False, False
    yield 'head-get-without-body', request(method=b'HEAD'), 200, {}, b'', True, False
    yield 'query-ignored-for-routing', request(path=b'/state?x=1'), 200, {}, INITIAL, False, False
    yield 'trailing-slash', request(path=b'/state/'), 404, {}, b'', False, False
    yield 'wrong-method', request(method=b'POST'), 405, {}, b'', False, False
    yield 'http10-without-host', request(host=b'', version=b'1.0'), 200, {}, INITIAL, False, True
    yield 'missing-host', request(host=b''), 400, {}, b'', False, True
    yield 'empty-host-presence', request(host=b'Host:\r\n'), 200, {}, INITIAL, False, False
    yield 'duplicate-host', request(extra=b'Host: other\r\n'), 400, {}, b'', False, True
    yield 'connection-close-token', request(extra=b'Connection: keep-alive, CLOSE \r\n'), 200, {}, INITIAL, False, True
    yield 'bare-lf', b'GET /state HTTP/1.1\n', 400, {}, b'', False, True
    yield 'obs-fold', request(extra=b' continuation\r\n'), 400, {}, b'', False, True
    yield 'sixteen-fields', request(extra=b'X: x\r\n' * 14), 200, {}, INITIAL, False, False
    yield 'seventeen-fields', request(extra=b'X: x\r\n' * 15), 431, {}, b'', False, True
    yield 'duplicate-length', request(extra=b'Content-Length: 0\r\n'), 400, {}, b'', False, True
    yield 'length-trailing-ows', request(framing=b'Content-Length: 0 \r\n'), 400, {}, b'', False, True
    yield 'cl-and-te', request(extra=b'Transfer-Encoding: chunked\r\n'), 400, {}, b'', False, True
    yield 'unsupported-transfer-coding', request(framing=b'Transfer-Encoding: gzip\r\n'), 501, {}, b'', False, True
    yield 'body-limit-prefix', request(framing=b'Content-Length: 1025\r\n'), 413, {}, b'', False, True
    yield 'request-line-limit-prefix', b'GET /' + b'a' * 1100, 414, {}, b'', False, True
    for label, extra, auth, status in [
        ('no-key-before-bad-body', b'', False, 401),
        ('valid-key-bad-body', b'', True, 400),
        ('wrong-key', b'Authorization: Bearer wrong\r\n', False, 401),
        ('bearer-case-sensitive', b'Authorization: bearer dev-key\r\n', False, 401),
        ('first-auth-wins-wrong', b'Authorization: Bearer wrong\r\n' + KEY, False, 401),
    ]:
        yield label, request(b'PUT', b'/setpoint', b'abc', extra, auth), status, {}, b'', False, False
    yield 'first-auth-wins-correct', request(b'PUT', b'/mode', b'heat', extra=b'Authorization: Bearer wrong\r\n', auth=True), 200, {'mode': 'heat', 'heater': True}, None, False, False
    yield 'header-name-case-insensitive', request(b'PUT', b'/mode', b'heat', extra=b'aUtHoRiZaTiOn: Bearer dev-key\r\n'), 200, {'mode': 'heat', 'heater': True}, None, False, False
    for label, body, status, fields in [
        ('plus-not-decimal', b'+199', 400, {}), ('minus-alone', b'-', 400, {}),
        ('six-digits', b'000199', 400, {}), ('five-leading-zero-digits', b'00199', 200, {'temp_dc': 199}),
        ('positive-i16-overflow', b'32768', 400, {}), ('negative-i16-overflow', b'-32769', 400, {}),
        ('form-feed-trimmed', b'\x0c199\x0c', 200, {'temp_dc': 199}),
        ('vertical-tab-not-trimmed', b'\x0b199', 400, {}),
    ]:
        yield label, request(b'POST', b'/temp', body, auth=True), status, fields, b'' if status != 200 else None, False, False
    yield 'typed-setpoint-refusal', request(b'PUT', b'/setpoint', b'49', auth=True), 422, {}, b'{"error":"setpoint_out_of_range"}', False, False
    yield 'typed-relay-refusal', request(b'PUT', b'/relay/4', b'on', auth=True), 404, {}, b'{"error":"no_such_relay"}', False, False
    yield 'unrepresentable-relay-index', request(b'PUT', b'/relay/256', b'on', auth=True), 404, {}, b'', False, False
    yield 'leading-zero-relay-index', request(b'PUT', b'/relay/0003', b'on', auth=True), 200, {'relays': [False, False, False, True]}, None, False, False
    yield 'chunked-mode', request(b'PUT', b'/mode', b'2\r\nhe\r\n2\r\nat\r\n0\r\n\r\n', auth=True, framing=b'Transfer-Encoding: chunked\r\n'), 200, {'mode': 'heat', 'heater': True}, None, False, False
    yield 'chunk-extension-rejected', request(b'PUT', b'/mode', b'4;x=y\r\nheat\r\n0\r\n\r\n', auth=True, framing=b'Transfer-Encoding: chunked\r\n'), 400, {}, b'', False, True
    yield 'chunk-body-limit-prefix', request(b'PUT', b'/mode', b'401\r', auth=True, framing=b'Transfer-Encoding: chunked\r\n'), 413, {}, b'', False, True


def run_case(qemu, elf, item):
    name, wire, status, fields, exact, head_only, close = item
    with tempfile.TemporaryDirectory(prefix='thermostat-http-') as tmp:
        uart = Path(tmp) / 'uart.sock'
        with (Path(tmp) / 'qemu.log').open('w+') as log:
            proc = subprocess.Popen([qemu, '-M', 'virt', '-cpu', 'rv32', '-m', '16M', '-smp', '1',
                '-bios', 'none', '-kernel', str(elf), '-display', 'none', '-monitor', 'none',
                '-serial', f'unix:{uart},server=on,wait=off'], stdout=log, stderr=log)
            try:
                deadline = time.monotonic() + 10
                while not uart.exists():
                    if proc.poll() is not None or time.monotonic() > deadline:
                        log.seek(0)
                        raise RuntimeError(log.read())
                    time.sleep(.02)
                with socket.socket(socket.AF_UNIX) as sock:
                    sock.settimeout(5)
                    sock.connect(str(uart))
                    sock.sendall(wire)
                    received = bytearray()
                    while b'\r\n\r\n' not in received:
                        part = sock.recv(4096)
                        assert part, (name, 'no response head')
                        received.extend(part)
                    end = received.index(b'\r\n\r\n') + 4
                    head = bytes(received[:end])
                    lines = head.decode('ascii').split('\r\n')
                    actual = int(lines[0].split()[1])
                    headers = dict(line.split(':', 1) for line in lines[1:] if ':' in line)
                    length = int(headers['Content-Length'])
                    body_len = 0 if head_only else length
                    while len(received) < end + body_len:
                        part = sock.recv(4096)
                        assert part, (name, 'short response body')
                        received.extend(part)
                    body = bytes(received[end:end + body_len])
                    assert actual == status, (name, actual, status, body)
                    assert (headers.get('Connection', '').strip().lower() == 'close') == close, (name, headers)
                    if exact is not None:
                        assert body == exact, (name, body, exact)
                    if head_only:
                        assert length == len(INITIAL) and len(received) == end, (name, length, received)
                        sock.settimeout(.1)
                        try:
                            extra = sock.recv(1)
                        except socket.timeout:
                            extra = b''
                        assert not extra, (name, 'unexpected HEAD body', extra)
                    if fields:
                        payload = json.loads(body)
                        assert all(payload[k] == v for k, v in fields.items()), (name, payload, fields)
                    return dict(name=name, request_hex=wire.hex(), status=actual,
                                response_head=head.decode('ascii'), response_body_hex=body.hex())
            finally:
                proc.terminate()
                proc.wait(timeout=10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV32', 'qemu-system-riscv32'))
    parser.add_argument('--out', type=Path, default=RV / 'build/thermostat-http-boundaries.json')
    args = parser.parse_args()
    job = json.loads((RV / 'jobs/thermostat-heater.json').read_text())
    elf = RV / job['elf']
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    assert digest == job['elf_sha256'], 'ELF differs from the proof job pin'
    records = [run_case(args.qemu, elf, case) for case in cases()]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(dict(elf_sha256=digest,
        qemu=subprocess.check_output([args.qemu, '--version'], text=True).splitlines()[0],
        fresh_machine_per_case=True, cases=records), indent=2) + '\n')
    print(f'PASS: {len(records)} raw UART HTTP boundary cases; ELF {digest}; {args.out}')


if __name__ == '__main__':
    main()
