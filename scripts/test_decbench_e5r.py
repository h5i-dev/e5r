"""Focused tests for the out-of-tree DecBench adapter."""

from __future__ import annotations

import os
import unittest
from unittest.mock import patch

from decbench_e5r import requested_addresses, variable_info


class TargetTests(unittest.TestCase):
    def test_both_decbench_target_spellings_are_honoured(self) -> None:
        self.assertEqual(
            requested_addresses([("one", 0x1000), ("two", 0x2000)], {0x3000}),
            {0x1000, 0x2000, 0x3000},
        )

    def test_default_single_function_api_uses_the_requested_name(self) -> None:
        from pathlib import Path

        from decbench_e5r import E5rDecompiler

        backend = E5rDecompiler()
        item = {
            "function": {"name": "sub_1000", "addr": "0x1000", "complete": True},
            "code": "uint64_t sub_1000(void) { return 1; }",
            "variables": [],
        }
        with (
            patch.object(backend, "_run", return_value=[item]),
            patch("decbench_e5r.common.elf_text_ranges", return_value=None),
            patch("decbench_e5r.common.should_skip_function", return_value=False),
        ):
            code = backend.decompile_function(Path("stripped.elf"), "source_name", 0x1000)
        self.assertEqual(code, item["code"])

    def test_target_mode_keeps_successes_when_one_address_fails(self) -> None:
        from pathlib import Path

        from decbench_e5r import E5rDecompiler

        backend = E5rDecompiler()
        item = {
            "function": {"name": "sub_2000", "addr": "0x2000", "complete": True},
            "code": "uint64_t sub_2000(void) { return 2; }",
            "variables": [],
        }

        def run(_binary: Path, target: str) -> list[dict]:
            if target == "0x1000":
                raise RuntimeError("one malformed function")
            return [item]

        with (
            patch.object(backend, "_run", side_effect=run),
            patch("decbench_e5r.common.elf_text_ranges", return_value=None),
            patch("decbench_e5r.common.should_skip_function", return_value=False),
            patch.dict(os.environ, {"E5R_MODE": "targets"}),
        ):
            result = backend.decompile_binary(
                Path("stripped.elf"),
                functions=[("bad", 0x1000), ("good", 0x2000)],
            )

        self.assertEqual(list(result.functions), ["good"])
        self.assertEqual(result.decompiler.failed_functions, ["bad"])


class VariableInfoTests(unittest.TestCase):
    def test_parameters_keep_abi_order_and_locals_keep_stack_offsets(self) -> None:
        got = variable_info(
            {
                "variables": [
                    {
                        "name": "arg0",
                        "type": "uint8_t *",
                        "size": 8,
                        "role": "parameter",
                        "storage": "register+56",
                    },
                    {
                        "name": "saved",
                        "type": "uint32_t",
                        "size": 4,
                        "role": "local",
                        "storage": "stack-12",
                        "stack_offset": -20,
                    },
                    {
                        "name": "reg40",
                        "type": "uint64_t",
                        "size": 8,
                        "role": "inherited",
                        "storage": "register+40",
                    },
                    {
                        "name": "arg1",
                        "type": "uint32_t",
                        "size": 4,
                        "role": "parameter",
                        "storage": "stack+16",
                        "argument": 7,
                    },
                ]
            }
        )

        self.assertEqual([v.name for v in got], ["arg0", "saved", "arg1"])
        self.assertEqual([v.arg_index for v in got], [0, None, 7])
        self.assertEqual([v.kind for v in got], ["arg", "stack", "arg"])
        # The numeric API field wins over the legacy display string. The
        # latter remains a fallback for output from older e5r versions.
        self.assertEqual([v.stack_offset for v in got], [None, -20, 16])

    def test_malformed_optional_fields_do_not_break_a_binary(self) -> None:
        got = variable_info(
            {
                "variables": [
                    {
                        "name": "v0",
                        "type": "uint64_t",
                        "size": "unknown",
                        "role": "local",
                        "storage": "stack?",
                    },
                    "not a record",
                ]
            }
        )

        self.assertEqual(len(got), 1)
        self.assertIsNone(got[0].size)
        self.assertIsNone(got[0].stack_offset)


if __name__ == "__main__":
    unittest.main()
