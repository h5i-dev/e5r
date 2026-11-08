#!/usr/bin/env python3
"""Exercise the proof job's exact ELF via QEMU virt's UART (Apache-2.0)."""
import argparse
import hashlib
import json
import os
import random
from pathlib import Path
import socket
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
RV = ROOT / 'verification/rv32'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV32', 'qemu-system-riscv32'))
    parser.add_argument('--random-cases', type=int, default=256)
    parser.add_argument('--out', type=Path, default=RV / 'build/thermostat-qemu.json')
    args = parser.parse_args()
    job = json.loads((RV / 'jobs/thermostat-heater.json').read_text())
    elf = RV / job['elf']
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    assert digest == job['elf_sha256'], 'ELF differs from the proof job pin'
    records = []
    with tempfile.TemporaryDirectory(prefix='thermostat-') as tmp:
        uart = Path(tmp) / 'uart.sock'
        with (Path(tmp) / 'qemu.log').open('w+') as log:
            proc = subprocess.Popen([
                args.qemu, '-M', 'virt', '-cpu', 'rv32', '-m', '16M', '-smp', '1',
                '-bios', 'none', '-kernel', str(elf), '-display', 'none', '-monitor', 'none',
                '-serial', f'unix:{uart},server=on,wait=off',
            ], stdout=log, stderr=log)
            try:
                deadline = time.monotonic() + 10
                while not uart.exists():
                    if proc.poll() is not None or time.monotonic() > deadline:
                        log.seek(0)
                        raise RuntimeError(log.read())
                    time.sleep(.02)
                with socket.socket(socket.AF_UNIX) as sock:
                    sock.settimeout(10)
                    sock.connect(str(uart))
                    buffered = bytearray()

                    def request(method, path, body='', status=200, key=True, **fields):
                        data = body.encode()
                        head = f'{method} {path} HTTP/1.1\r\nHost: thermostat\r\nContent-Length: {len(data)}\r\n'
                        if key:
                            head += 'Authorization: Bearer dev-key\r\n'
                        sock.sendall(head.encode() + b'\r\n' + data)
                        while b'\r\n\r\n' not in buffered:
                            chunk = sock.recv(4096)
                            assert chunk, 'UART closed before response headers'
                            buffered.extend(chunk)
                        boundary = buffered.index(b'\r\n\r\n') + 4
                        lines = bytes(buffered[:boundary]).decode().split('\r\n')
                        actual = int(lines[0].split()[1])
                        length = next(int(line.split(':', 1)[1]) for line in lines[1:] if line.lower().startswith('content-length:'))
                        while len(buffered) < boundary + length:
                            chunk = sock.recv(4096)
                            assert chunk, 'UART closed before response body'
                            buffered.extend(chunk)
                        payload = json.loads(bytes(buffered[boundary:boundary + length])) if length else None
                        del buffered[:boundary + length]
                        assert actual == status, (path, actual, status, payload)
                        for k, v in fields.items():
                            assert payload[k] == v, (path, k, payload[k], v)
                        records.append(dict(method=method, path=path, body=body, status=actual, response=payload))

                    request('GET', '/state', key=False, heater=False, mode='off', setpoint_dc=200)
                    request('PUT', '/mode', 'heat', key=False, status=401)
                    request('PUT', '/mode', 'heat', heater=True)
                    request('POST', '/temp', '349', heater=True)
                    request('POST', '/temp', '350', heater=False)
                    request('POST', '/temp', '32767', heater=False)
                    request('POST', '/temp', '-32768', heater=True)
                    request('PUT', '/mode', 'auto', heater=True)
                    request('POST', '/temp', '200', heater=False)
                    request('POST', '/temp', '199', heater=True)
                    request('PUT', '/setpoint', '49', status=422)
                    request('PUT', '/setpoint', '301', status=422)
                    request('PUT', '/setpoint', '50', heater=False, setpoint_dc=50)
                    request('PUT', '/setpoint', '300', heater=True, setpoint_dc=300)
                    request('PUT', '/relay/3', 'on', relays=[False, False, False, True])
                    request('PUT', '/relay/4', 'on', status=404)
                    request('PUT', '/relay/255', 'on', status=404)
                    request('PUT', '/mode', 'off', heater=False)
                    request('GET', '/state', key=False, heater=False, mode='off', setpoint_dc=300,
                            temp_dc=199, relays=[False, False, False, True])
                    # Independent state-machine oracle, including failed writes and persistence.
                    rng = random.Random(0xE552)
                    state = dict(setpoint_dc=300, temp_dc=199, heater=False,
                                 relays=[False, False, False, True], mode='off')
                    for _ in range(args.random_cases):
                        action = rng.choice(['mode', 'temp', 'setpoint', 'relay', 'read'])
                        key = rng.randrange(8) != 0
                        status = 200
                        if action == 'read':
                            request('GET', '/state', key=False, **state)
                            continue
                        if action == 'mode':
                            method, path, body = 'PUT', '/mode', rng.choice(['off', 'heat', 'auto'])
                            if key:
                                state['mode'] = body
                        elif action == 'temp':
                            value = rng.choice([-32768, 349, 350, 32767, rng.randint(-32768, 32767)])
                            method, path, body = 'POST', '/temp', str(value)
                            if key:
                                state['temp_dc'] = value
                        elif action == 'setpoint':
                            value = rng.choice([49, 50, 300, 301, rng.randint(-32768, 32767)])
                            method, path, body = 'PUT', '/setpoint', str(value)
                            if key and 50 <= value <= 300:
                                state['setpoint_dc'] = value
                            elif key:
                                status = 422
                        else:
                            index = rng.choice([0, 1, 2, 3, 4, 255])
                            on = bool(rng.getrandbits(1))
                            method, path, body = 'PUT', f'/relay/{index}', 'on' if on else 'off'
                            if key and index < 4:
                                state['relays'][index] = on
                            elif key:
                                status = 404
                        if not key:
                            status = 401
                        elif status == 200 and action != 'relay':
                            state['heater'] = state['temp_dc'] < 350 and (
                                state['mode'] == 'heat' or (
                                    state['mode'] == 'auto' and state['temp_dc'] < state['setpoint_dc']))
                        request(method, path, body, key=key, status=status,
                                **(state if status == 200 else {}))
                        if status != 200:
                            request('GET', '/state', key=False, **state)

            finally:
                proc.terminate()
                proc.wait(timeout=10)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(dict(elf_sha256=digest,
        qemu=subprocess.check_output([args.qemu, '--version'], text=True).splitlines()[0],
        random_seed=0xE552, random_commands=args.random_cases, cases=records), indent=2) + '\n')
    print(f'PASS: {len(records)} UART HTTP cases; ELF {digest}; {args.out}')


if __name__ == '__main__':
    main()
