#!/usr/bin/env python3
"""Regenerate observed instruction expectations; e5r independently kernel-checks them."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RV = ROOT / 'verification/rv32'
HEADER = '''-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--http-parse', action='store_true', help='check all actual strict HTTP head parser instructions')
    parser.add_argument('--main-chunk', action='store_true', help='check actual main chunk initialization/call/store/dispatch instructions')
    parser.add_argument('--main-chunk-receive', action='store_true', help='check actual exhausted-body buffer setup and UART poll')
    parser.add_argument('--main-chunk-capacity', action='store_true', help='check actual raw-buffer-capacity error status setup')
    parser.add_argument('--chunk-step', action='store_true', help='check actual byte-wise chunked body decoder')
    parser.add_argument('--shell', action='store_true', help='check the concrete caller/wrapper regions')
    parser.add_argument('--commit', action='store_true', help='check successful-result marshalling and state persistence')
    parser.add_argument('--release-borrow', action='store_true', help='check the rejected-command borrow release')
    parser.add_argument('--reply', action='store_true', help='check the cached reply restoration')
    parser.add_argument('--acquire', action='store_true', help='check actual write-handler borrow acquisition')
    parser.add_argument('--boot', action='store_true', help='check actual reset entry instructions')
    parser.add_argument('--init', action='store_true', help='check main prologue and App initialization')
    parser.add_argument('--read-shell', action='store_true', help='check the separate inlined Read handler call site')
    parser.add_argument('--outer-return', action='store_true', help='check the write-handler outer epilogue')
    parser.add_argument('--read-engine', action='store_true', help='check distinct Read marshalling and persistence')
    parser.add_argument('--zero-init', action='store_true', help='check actual startup memset instructions')
    parser.add_argument('--loop-init', action='store_true', help='check main routes and buffer call setup')
    parser.add_argument('--uart-poll', action='store_true', help='check the actual receive/transmit wait instructions')
    parser.add_argument('--future-init', action='store_true', help='check main serve Future initialization and first parser call')
    parser.add_argument('--head-empty', action='store_true', help='check parse_head empty-input path including real prologue/epilogue')
    parser.add_argument('--read-more', action='store_true', help='check main incomplete-header dispatch to receive polling')
    parser.add_argument('--decimal', action='store_true', help='check original application parse_i16')
    parser.add_argument('--trim', action='store_true', help='check actual decoder body trim loops')
    parser.add_argument('--decode', action='store_true', help='check actual Wire path/body/result dispatcher')
    parser.add_argument('--write-char', action='store_true', help='check actual Cursor write_char instructions')
    parser.add_argument('--format-str', action='store_true', help='check actual default Formatter write_str path')
    parser.add_argument('--bool-format', action='store_true', help='check actual bool Display literal dispatch')
    parser.add_argument('--memcpy', action='store_true', help='check actual memcpy trampoline and all copy paths')
    parser.add_argument('--cursor', action='store_true', help='check actual Cursor write_str')
    parser.add_argument('--refusal', action='store_true', help='check actual refused/missing request return setup')
    parser.add_argument('--write-handler', action='store_true', help='check actual write-handler prologue, Future extraction and response stores')
    parser.add_argument('--header-call', action='store_true', help='check actual header query setup and call')
    parser.add_argument('--write-entry', action='store_true', help='check actual principal load/store and decoder call')
    parser.add_argument('--header', action='store_true', help='check actual Request header lookup/casefold/return instructions')
    parser.add_argument('--memcmp', action='store_true', help='check actual memcmp byte loop and return')
    parser.add_argument('--bearer', action='store_true', help='check actual missing/short/Bearer-prefix caller')
    parser.add_argument('--auth-compare', action='store_true', help='check actual authentication key-length and OR/XOR loop')
    parser.add_argument('--wire-caller', action='store_true', help='check actual decoder-result unpack and command stack stores')
    parser.add_argument('--param', action='store_true', help='check actual Request param_u32 leaf')
    parser.add_argument('--pad-integral', action='store_true', help='check actual default pad_integral path')
    parser.add_argument('--write-prefix', action='store_true', help='check actual write_prefix function')
    parser.add_argument('--i16-display', action='store_true', help='check actual signed i16 Display instructions')
    parser.add_argument('--slice-format', action='store_true', help='check actual slice and str Display wrappers')
    parser.add_argument('--format-engine', action='store_true', help='check actual compact JSON Formatter loop')
    parser.add_argument('--encode-reply', action='store_true', help='check actual wire reply encoder')
    parser.add_argument('--write-success', action='store_true', help='check actual successful write-handler encoder call and dispatch')
    parser.add_argument('--encode-error', action='store_true', help='check actual error encoder and all enum branches')
    parser.add_argument('--write-error', action='store_true', help='check actual kernel-refused write encoder call and dispatch')
    parser.add_argument('--read-reply', action='store_true', help='check actual separate Read reply encoding and completion')
    parser.add_argument('--shared-response', action='store_true', help='check actual shared response-object construction')
    parser.add_argument('--uart-tx-byte', action='store_true', help='check actual UART data load, THR store and loop branch')
    parser.add_argument('--uart-write-all', action='store_true', help='check actual UART write_all Future')
    parser.add_argument('--http-put', action='store_true', help='check actual HTTP header byte append')
    parser.add_argument('--http-reason', action='store_true', help='check actual HTTP reason phrases in bounded-memory chunks')
    parser.add_argument('--http-decimal', action='store_true', help='check actual bounded-body HTTP decimal encoder instructions')
    parser.add_argument('--response-head', action='store_true', help='check actual HTTP write_head entry, validation, calls and return instructions')
    parser.add_argument('--send-future', action='store_true', help='check actual fresh HTTP send future, UART call sites, flush/result and return instructions')
    parser.add_argument('--send-caller', action='store_true', help='check actual main send-future caller instructions')
    parser.add_argument('--main-completion', action='store_true', help='check actual main completed-send result and close dispatch instructions')
    parser.add_argument('--main-write', action='store_true', help='check actual main write-handler call and completed Response extraction')
    args = parser.parse_args()
    if sum([args.http_parse, args.main_chunk, args.main_chunk_receive, args.main_chunk_capacity, args.chunk_step, args.main_write, args.send_caller, args.main_completion, args.send_future, args.response_head, args.http_decimal, args.http_put, args.http_reason, args.uart_tx_byte, args.uart_write_all, args.read_reply, args.shared_response, args.encode_error, args.write_error, args.write_success, args.format_engine, args.encode_reply, args.slice_format, args.pad_integral, args.write_prefix, args.i16_display, args.shell, args.commit, args.release_borrow, args.reply, args.acquire, args.boot, args.init, args.read_shell, args.outer_return, args.read_engine, args.zero_init, args.loop_init, args.uart_poll, args.future_init, args.head_empty, args.read_more, args.decimal, args.trim, args.decode, args.param, args.wire_caller, args.auth_compare, args.memcmp, args.bearer, args.header, args.header_call, args.write_entry, args.write_handler, args.refusal, args.memcpy, args.cursor, args.format_str, args.bool_format, args.write_char]) > 1:
        parser.error('choose only one instruction region')
    job = json.loads((RV / 'jobs/thermostat-heater.json').read_text())
    elf = RV / job['elf']
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    assert digest == job['elf_sha256'], 'ELF differs from the reviewed job pin'
    assert f'ELF sha256 {digest},' in (RV / 'Projects/thermostat/Image.lean').read_text(), 'Run e5r check to export this ELF first'
    symbols = {}
    for line in subprocess.check_output(['llvm-nm', '-S', '--defined-only', str(elf)], text=True).splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[3] in {'thermostat_transition', 'thermostat_apply', 'thermostat_read_only'}:
            symbols[parts[3]] = (int(parts[0], 16), int(parts[1], 16))
    assert len(symbols) == 3, 'Kernel ABI symbols missing'
    start = min(a for a, _ in symbols.values())
    end = max(a + n for a, n in symbols.values())
    ranges = ([(0x80002c46, 0x80003584)] if args.http_parse
              else [(0x80000e54, 0x80000f8c)] if args.main_chunk
              else [(0x80000f8c, 0x80000fc0)] if args.main_chunk_receive
              else [(0x80001bb0, 0x80001bbc)] if args.main_chunk_capacity
              else [(0x80002998, 0x80002c46)] if args.chunk_step
              else [(0x8000195a, 0x80001976), (0x80001998, 0x800019b8)] if args.main_write
              else [(0x80001772, 0x80001784)] if args.send_caller
              else [(0x80001784, 0x8000178c), (0x800017aa, 0x800017be)] if args.main_completion
              else [(0x8000030e, 0x800004c6)] if args.send_future
              else [(0x80003e4e, 0x80004122)] if args.response_head
              else [(0x80004180, 0x80004514)] if args.http_decimal
              else [(0x80004122, 0x80004180)] if args.http_put
              else [(0x80003584, 0x80003e4e)] if args.http_reason
              else [(0x800007ea, 0x800007f8)] if args.uart_tx_byte
              else [(0x80000786, 0x8000085c)] if args.uart_write_all
              else [(0x80001b5e, 0x80001bb0)] if args.read_reply
              else [(0x80001704, 0x80001772)] if args.shared_response
              else [(0x80001e4a, 0x80001eb8)] if args.encode_error
              else [(0x80000652, 0x80000678)] if args.write_error
              else [(0x80000736, 0x80000766)] if args.write_success
              else [(0x80004976, 0x80004b34)] if args.format_engine
              else [(0x80001eb8, 0x80001f6e)] if args.encode_reply
              else [(0x8000228c, 0x800022a0), (0x8000513e, 0x8000514e)] if args.slice_format
              else [(0x80004514, 0x8000455c), (0x800045b2, 0x800045f0), (0x8000469a, 0x800046c2)] if args.pad_integral
              else [(0x80004e00, 0x80004e5e)] if args.write_prefix
              else [(0x80004e5e, 0x80004fa4)] if args.i16_display
              else [(0x80002302, 0x800023de)] if args.write_char
              else [(0x80004790, 0x800047bc), (0x8000486c, 0x80004892)] if args.format_str
              else [(0x80005112, 0x8000513e)] if args.bool_format
              else [(0x80005182, 0x80005310)] if args.memcpy
              else [(0x800022a0, 0x80002302)] if args.cursor
              else [(0x800005a2, 0x800005aa)] if args.refusal
              else [(0x800004c6, 0x8000052e), (0x800005aa, 0x800005c4)] if args.write_handler
              else [(0x8000052e, 0x80000542)] if args.header_call
              else [(0x800005e2, 0x800005f4)] if args.write_entry
              else [(0x800026c0, 0x8000278a)] if args.header
              else [(0x80005162, 0x80005182)] if args.memcmp
              else [(0x80000542, 0x80000568)] if args.bearer
              else [(0x80000568, 0x800005a2)] if args.auth_compare
              else [(0x800005f4, 0x80000614)] if args.wire_caller
              else [(0x8000278a, 0x80002814)] if args.param
              else [(0x80001fb4, 0x8000210e), (0x80002136, 0x8000228c)] if args.decode
              else [(0x80001f6e, 0x80001fb4), (0x8000210e, 0x80002136)] if args.trim
              else [(0x80001dae, 0x80001e26)] if args.decimal
              else [(0x80000a26, 0x80000a7e)] if args.read_more
              else [(0x80002c46, 0x80002c8a), (0x80002ce6, 0x80002cf4), (0x80002d6a, 0x80002da2)] if args.head_empty
              else [(0x80000978, 0x80000a26)] if args.future_init
              else [(0x800007f8, 0x8000080a), (0x80000b9e, 0x80000bb2)] if args.uart_poll
              else [(0x800008d8, 0x80000964)] if args.loop_init
              else [(0x80005638, 0x800056a0)] if args.zero_init
              else [(0x80001a7e, 0x80001b5e)] if args.read_engine
              else [(0x800005c4, 0x800005e2)] if args.outer_return
              else [(0x80001a08, 0x80001a4c)] if args.read_shell
              else [(0x80000000, 0x80000036)] if args.boot
              else [(0x80000862, 0x800008d8)] if args.init
              else [(0x80000614, 0x80000622)] if args.acquire
              else [(0x8000071c, 0x80000736)] if args.reply
              else [(0x80000648, 0x80000652)] if args.release_borrow
              else [(0x80000678, 0x8000071c), (0x80001e38, 0x80001e4a)] if args.commit
              else [(0x80000622, 0x80000648), (0x80001e26, 0x80001e38)] if args.shell
              else [(start, end)])
    prefix = 'hh' if args.http_parse else 'cc' if args.main_chunk else 'cr' if args.main_chunk_receive else 'cf' if args.main_chunk_capacity else 'ck' if args.chunk_step else 'mw' if args.main_write else 'snc' if args.send_caller else 'mcp' if args.main_completion else 'se' if args.send_future else 'rh' if args.response_head else 'de' if args.http_decimal else 'hp' if args.http_put else 'rp' if args.http_reason else 'tx' if args.uart_tx_byte else 'uw' if args.uart_write_all else 'rr' if args.read_reply else 'sr' if args.shared_response else 'ee' if args.encode_error else 'er' if args.write_error else 'ws' if args.write_success else 'fe' if args.format_engine else 'ej' if args.encode_reply else 'sf' if args.slice_format else 'pi' if args.pad_integral else 'wp' if args.write_prefix else 'di' if args.i16_display else 'ch' if args.write_char else 'fs' if args.format_str else 'bf' if args.bool_format else 'cp' if args.memcpy else 'cu' if args.cursor else 'rf' if args.refusal else 'wh' if args.write_handler else 'hq' if args.header_call else 'we' if args.write_entry else 'hd' if args.header else 'mc' if args.memcmp else 'be' if args.bearer else 'au' if args.auth_compare else 'wc' if args.wire_caller else 'pm' if args.param else 'wd' if args.decode else 'tr' if args.trim else 'dc' if args.decimal else 'mo' if args.read_more else 'he' if args.head_empty else 'fu' if args.future_init else 'up' if args.uart_poll else 'li' if args.loop_init else 'ze' if args.zero_init else 're' if args.read_engine else 'ep' if args.outer_return else 'rs' if args.read_shell else 'bt' if args.boot else 'ini' if args.init else 'ac' if args.acquire else 'v' if args.reply else 'u' if args.release_borrow else 't' if args.commit else 's' if args.shell else 'd'
    module = 'HttpParseCode.lean' if args.http_parse else 'MainChunkCode.lean' if args.main_chunk else 'MainChunkReceiveCode.lean' if args.main_chunk_receive else 'MainChunkCapacityCode.lean' if args.main_chunk_capacity else 'ChunkCode.lean' if args.chunk_step else 'MainWriteCode.lean' if args.main_write else 'SendCallerCode.lean' if args.send_caller else 'MainCompletionCode.lean' if args.main_completion else 'SendCode.lean' if args.send_future else 'ResponseHeadCode.lean' if args.response_head else 'HttpDecCode.lean' if args.http_decimal else 'HttpPutCode.lean' if args.http_put else 'HttpReasonCode.lean' if args.http_reason else 'UartTxCode.lean' if args.uart_tx_byte else 'UartWriteCode.lean' if args.uart_write_all else 'ReadReplyCode.lean' if args.read_reply else 'SharedResponseCode.lean' if args.shared_response else 'EncodeErrorCode.lean' if args.encode_error else 'WriteErrorCode.lean' if args.write_error else 'WriteSuccessCode.lean' if args.write_success else 'FormatEngineCode.lean' if args.format_engine else 'EncodeReplyCode.lean' if args.encode_reply else 'SliceFormatCode.lean' if args.slice_format else 'IntegralCode.lean' if args.pad_integral else 'WritePrefixCode.lean' if args.write_prefix else 'I16Code.lean' if args.i16_display else 'WriteCharCode.lean' if args.write_char else 'FormatStrCode.lean' if args.format_str else 'BoolFormatCode.lean' if args.bool_format else 'MemcpyCode.lean' if args.memcpy else 'CursorCode.lean' if args.cursor else 'RefusalCode.lean' if args.refusal else 'WriteHandlerCode.lean' if args.write_handler else 'HeaderCallerCode.lean' if args.header_call else 'WriteEntryCode.lean' if args.write_entry else 'HeaderCode.lean' if args.header else 'MemcmpCode.lean' if args.memcmp else 'BearerCode.lean' if args.bearer else 'AuthCode.lean' if args.auth_compare else 'WireCallerCode.lean' if args.wire_caller else 'ParamCode.lean' if args.param else 'DecodeCode.lean' if args.decode else 'TrimCode.lean' if args.trim else 'DecimalCode.lean' if args.decimal else 'ReadMoreCode.lean' if args.read_more else 'HeadEmptyCode.lean' if args.head_empty else 'FutureCode.lean' if args.future_init else 'UartPollCode.lean' if args.uart_poll else 'LoopInitCode.lean' if args.loop_init else 'ZeroCode.lean' if args.zero_init else 'ReadEngineCode.lean' if args.read_engine else 'OuterReturnCode.lean' if args.outer_return else 'ReadShellCode.lean' if args.read_shell else 'BootCode.lean' if args.boot else 'InitCode.lean' if args.init else 'AcquireCode.lean' if args.acquire else 'ReplyCode.lean' if args.reply else 'ReleaseCode.lean' if args.release_borrow else 'CommitCode.lean' if args.commit else 'ShellCode.lean' if args.shell else 'KernelCode.lean'
    lean_ranges = '[' + ','.join(f'({lo},{hi})' for lo, hi in ranges) + ']'
    tool = f'''import Projects.thermostat.ImageFidelity
import Theories.Logic
open E5R
#eval do
  let img := E5R.ThermostatImage.image.ro
  for (lo, hi) in {lean_ranges} do
    let mut pc : Nat := lo
    while pc < hi do
      match fetchDecode img (BitVec.ofNat 32 pc) with
      | none => throw (IO.userError s!"decode failed {{pc}}")
      | some (i, len) =>
        let some (bits, _) := fetch img (BitVec.ofNat 32 pc)
          | throw (IO.userError s!"fetch failed {{pc}}")
        IO.println s!"theorem {prefix}{{pc}} : fetchDecode img {{pc}}#32 = some ({{reprStr i}}, {{len.toNat}}#32) := by exact PackedFetch.fetchDecode_of {{pc}}#32 (by decide) (by decide) (bits := {{reprStr bits}}) (by decide +kernel) (by decide +kernel)"
        pc := pc + len.toNat
'''
    (RV / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='thermostat-decode-', dir=RV / 'build') as tmp:
        path = Path(tmp) / 'Observe.lean'
        path.write_text(tool)
        output = subprocess.check_output(['elan', 'run', 'leanprover/lean4:v4.35.0', 'lean', '-j1', str(path)],
                                         cwd=RV, env=dict(os.environ, LEAN_PATH='.'), text=True)
    assert all(line.startswith('theorem ' + prefix) for line in output.splitlines()), output
    header = HEADER if not (args.main_chunk or args.http_parse) else HEADER.replace('-- Expected instructions generated from observation; Lean checks every byte against the ELF.', '-- Observed instructions; kernel checked against the pinned ELF.')
    code = header + output + '\nend E5R.Thermostat\n'
    if args.check:
        if args.http_parse or args.main_chunk or args.chunk_step or args.http_reason or args.http_decimal or args.response_head or args.send_future:
            chunk_stem = "HttpParseCode" if args.http_parse else "MainChunkCode" if args.main_chunk else "ChunkCode" if args.chunk_step else "SendCode" if args.send_future else "ResponseHeadCode" if args.response_head else "HttpDecCode" if args.http_decimal else "HttpReasonCode"
            lines = output.splitlines()
            names = []
            chunk_size = 75 if args.chunk_step or args.main_chunk or args.http_parse else 100
            for offset in range(0, len(lines), chunk_size):
                name = f'{chunk_stem}{offset//chunk_size:02d}'
                names.append(name)
                expected = header + '\n'.join(lines[offset:offset+chunk_size]) + ('\n' if args.main_chunk or args.http_parse else '\n\n') + 'end E5R.Thermostat\n'
                assert expected == (RV / 'Projects/thermostat' / (name+'.lean')).read_text(), name+' expectations differ'
            expected_imports = ''.join('import Projects.thermostat.'+name+'\n' for name in names)
            assert expected_imports == (RV / 'Projects/thermostat' / module).read_text(), 'Chunk imports differ'
        else:
            assert code == (RV / 'Projects/thermostat' / module).read_text(), 'Instruction expectations differ'
        print(f'PASS: {len(output.splitlines())} instruction expectations match the pinned ELF')
    else:
        print(code, end='')


if __name__ == '__main__':
    main()
