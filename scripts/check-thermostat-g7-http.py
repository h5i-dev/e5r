#!/usr/bin/env python3
"""Check generic-framing route/write joins on the unchanged ELF (Apache-2.0)."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RV = ROOT / 'verification/rv32'
spec = importlib.util.spec_from_file_location('thermostat_http', ROOT / 'scripts/check-thermostat-http.py')
http = importlib.util.module_from_spec(spec)
spec.loader.exec_module(http)
INITIAL = dict(setpoint_dc=200, temp_dc=200, heater=False, relays=[False]*4, mode='off')


def snapshot(**changes):
    return json.dumps({**INITIAL, **changes}, separators=(',', ':')).encode()


def cases():
    writes = [
        ('setpoint', b'PUT /setpoint', b'250', True, 200, snapshot(setpoint_dc=250)),
        ('temp', b'POST /temp', b'350', True, 200, snapshot(temp_dc=350)),
        ('mode', b'PUT /mode', b'heat', True, 200, snapshot(mode='heat', heater=True)),
        ('range', b'PUT /setpoint', b'49', True, 422, b'{"error":"setpoint_out_of_range"}'),
        ('no-auth', b'POST /temp', b'350', False, 401, b''),
        ('malformed', b'PUT /mode', b'x', True, 400, b''),
        ('relay3', b'PUT /relay/3', b'on', True, 200, snapshot(relays=[False, False, False, True])),
        ('relay4', b'PUT /relay/4', b'on', True, 404, b'{"error":"no_such_relay"}'),
        ('relay256', b'PUT /relay/256', b'on', True, 404, b''),
    ]
    for label, command, body, auth, status, expected in writes:
        wire = (command+b' HTTP/1.1\r\nHost: x\r\n'+(http.KEY if auth else b'')+
                b'Transfer-Encoding: chunked\r\n\r\n'+format(len(body), 'x').encode()+
                b'\r\n'+body+b'\r\n0\r\n\r\n')
        yield label, wire, status, {}, expected, False, False
    for chunked in [False, True]:
        wire = (b'GET /relay/3 HTTP/1.1\r\nHost: x\r\n'+
                (b'Transfer-Encoding: chunked\r\n' if chunked else b'')+b'\r\n'+
                (b'2\r\non\r\n0\r\n\r\n' if chunked else b''))
        yield f'relay-method-{chunked}', wire, 405, {}, b'', False, False
        for wrong_method in [False, True]:
            command = b'POST /state' if wrong_method else b'PUT /relay/3/x'
            wire = (command+b' HTTP/'+(b'1.1' if chunked else b'1.0')+b'\r\nHost: x\r\n'+
                    (b'Transfer-Encoding: chunked\r\n' if chunked else b'')+b'\r\n'+
                    (b'2\r\n-1\r\n0\r\n\r\n' if chunked else b''))
            yield f'route-refusal-{chunked}-{wrong_method}', wire, 405 if wrong_method else 404, {}, b'', False, not chunked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV32', 'qemu-system-riscv32'))
    parser.add_argument('--out', type=Path, default=RV / 'build/thermostat-g7-http.json')
    args = parser.parse_args()
    job = json.loads((RV / 'jobs/thermostat-heater.json').read_text())
    elf = RV / job['elf']
    sha = hashlib.sha256(elf.read_bytes()).hexdigest()
    assert sha == job['elf_sha256']
    reasons = {200: 'OK', 400: 'Bad Request', 401: 'Unauthorized', 404: 'Not Found', 405: 'Method Not Allowed', 422: 'Unprocessable Content'}
    fixtures = list(cases())
    records = []
    for case in fixtures:
        record = http.run_case(args.qemu, elf, case)
        expected = (f'HTTP/1.1 {case[2]} {reasons[case[2]]}\r\n'+
                    ('Content-Type: application/json\r\n' if case[4] else '')+
                    f'Content-Length: {len(case[4])}\r\n'+('Connection: close\r\n' if case[6] else '')+'\r\n')
        assert record['response_head'] == expected, (case[0], record['response_head'], expected)
        records.append(record)
        print(case[0], 'PASS exact header/body', flush=True)
    first = fixtures[0]
    wrong = (first[0], first[1], first[2], first[3], snapshot(setpoint_dc=249), first[5], first[6])
    try:
        http.run_case(args.qemu, elf, wrong)
    except AssertionError as error:
        assert first[0] in str(error), str(error)
        negative = {'name': 'wrong-committed-setpoint', 'status': 'SEMANTIC_REJECTION', 'detail': str(error)}
    else:
        raise AssertionError('wrong committed-state response was accepted')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps({'status': 'PASS', 'elf_sha256': sha,
        'qemu': subprocess.check_output([args.qemu, '--version'], text=True).splitlines()[0],
        'fresh_machine_per_case': True, 'cases': records, 'negative': negative}, indent=2)+'\n')
    print(f'PASS {len(records)} actual route/write cases and wrong-state expectation', flush=True)


if __name__ == '__main__':
    main()
