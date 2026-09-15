"""DecBench backend for e5r, living outside the DecBench checkout.

DecBench's plugin contract (its `docs/decompilers.md`) is one class implementing
`Decompiler` and a `@register_decompiler` call; an out-of-tree backend only has
to be imported before the registry is consulted, which `scripts/decbench_run.py`
does. Keeping the class here rather than in the DecBench tree means the
benchmark checkout stays exactly as upstream shipped it.

e5r has no Python API, so the backend shells out to the CLI. One
`e5r decompile <binary> all --json` call per binary is far cheaper than one
call per function: every invocation re-analyzes the whole image from scratch,
so `all` amortizes the analysis over every function instead of paying it
per function (3.4s for 193 functions of zlib's `example`, against 3.4s each).
Set E5R_MODE=targets to invoke once per requested address instead, which is
only useful when a binary is too large to decompile whole.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any

from decbench.decompilers.base import Decompiler, DecompilerConfig
from decbench.decompilers.raw import common
from decbench.decompilers.registry import register_decompiler
from decbench.models.decompilation import (
    DecompilationResult,
    DecompilerMetadata,
    FunctionDecompilation,
)

_REPO = Path(__file__).resolve().parent.parent


def e5r_binary() -> Path | None:
    """The e5r executable: $E5R, the release build, or one on $PATH."""
    env = os.environ.get("E5R")
    if env:
        p = Path(env).expanduser()
        return p if p.is_file() and os.access(p, os.X_OK) else None
    built = _REPO / "target" / "release" / "e5r"
    if built.is_file() and os.access(built, os.X_OK):
        return built
    found = shutil.which("e5r")
    return Path(found) if found else None


@register_decompiler("e5r")
class E5rDecompiler(Decompiler):
    """e5r driven through its JSON command line."""

    name = "e5r"
    display_name = "e5r"

    def __init__(self, config: DecompilerConfig | None = None):
        super().__init__(config)
        self._bin = e5r_binary()

    def is_available(self) -> bool:
        if self._bin is None:
            return False
        try:
            return subprocess.run([str(self._bin), "--version"], capture_output=True).returncode == 0
        except OSError:
            return False

    def get_version(self) -> str | None:
        if self._bin is None:
            return None
        try:
            out = subprocess.run(
                [str(self._bin), "--version"], capture_output=True, text=True
            ).stdout.strip()
        except OSError:
            return None
        version = out.split()[-1] if out else "unknown"
        rev = subprocess.run(
            ["git", "-C", str(_REPO), "rev-parse", "--short", "HEAD"],
            capture_output=True,
            text=True,
        )
        if rev.returncode == 0 and rev.stdout.strip():
            return f"{version}+{rev.stdout.strip()}"
        return version

    def decompile_binary(
        self,
        binary_path: Path,
        functions: list[tuple[str, int]] | None = None,
        output_dir: Path | None = None,
        function_names: set[int] | None = None,
        progress_path: Path | None = None,
    ) -> DecompilationResult:
        if self._bin is None:
            raise RuntimeError("e5r is not available: build it with cargo build --release")

        start = time.time()
        # e5r reports a function's virtual address, which for an ELF is already
        # the file-space address DecBench keys DWARF on, so no rebasing is needed.
        text_range = common.elf_text_ranges(binary_path)
        addr_targets = common.addr_targets_of(function_names)

        decompiled: dict[str, FunctionDecompilation] = {}
        failed: list[str] = []

        def _meta(partial: bool, error: str = "") -> DecompilerMetadata:
            extra: dict[str, Any] = {"backend": "e5r", "via": "cli"}
            if partial:
                extra["partial"] = True
            if error:
                extra["error"] = error
            return DecompilerMetadata(
                decompiler_name=self.id,
                decompiler_version=self.get_version(),
                total_time_seconds=time.time() - start,
                failed_functions=list(failed),
                extra=extra,
            )

        def _result(partial: bool, error: str = "") -> DecompilationResult:
            return DecompilationResult(
                binary_path=binary_path,
                binary_name=binary_path.stem,
                decompiler=_meta(partial, error),
                functions=dict(decompiled),
                output_dir=output_dir,
            )

        targets_mode = os.environ.get("E5R_MODE") == "targets" and addr_targets
        try:
            if targets_mode:
                items = []
                for addr in sorted(addr_targets):
                    items.extend(self._run(binary_path, hex(addr)))
            else:
                items = self._run(binary_path, "all")
        except Exception as e:  # noqa: BLE001
            failed.append("all")
            return _result(partial=False, error=str(e))

        candidates: list[tuple[str, int, dict]] = []
        for item in items:
            func = item.get("function") or {}
            name = str(func.get("name") or "")
            try:
                addr = int(str(func.get("addr")), 16)
            except (TypeError, ValueError):
                continue
            if common.should_skip_function(name, addr, text_range, addr_targets):
                continue
            candidates.append((name, addr, item))

        by_addr = {addr: (name, item) for name, addr, item in candidates}
        narrowed = common.narrow_to_source(
            [(name, addr) for name, addr, _ in candidates],
            function_names,
            backend=self.name,
            binary_name=binary_path.name,
        )

        for name, addr in narrowed:
            entry = by_addr.get(addr)
            code = (entry[1].get("code") or "") if entry else ""
            if not code.strip():
                failed.append(name)
                continue
            item = entry[1]
            metadata = common.extract_metrics(code)
            # e5r counts its own gotos and the constructs it could not model;
            # both say how much of the function it actually structured.
            metadata["e5r_gotos"] = item.get("gotos")
            metadata["e5r_unmodelled"] = item.get("unmodelled")
            metadata["e5r_complete"] = (item.get("function") or {}).get("complete")
            decompiled[name] = FunctionDecompilation(
                name=name,
                address=addr,
                decompiled_code=code,
                line_count=code.count("\n") + 1,
                variables=[],
                metadata=metadata,
            )
            if progress_path is not None:
                common.dump_progress(progress_path, _result(partial=True))

        result = _result(partial=False)
        if output_dir:
            output_dir.mkdir(parents=True, exist_ok=True)
            result.to_c_file(output_dir / f"{self.name}_{binary_path.stem}.c")
            result.to_toml(output_dir / f"{self.name}_{binary_path.stem}.toml")
        return result

    def _run(self, binary_path: Path, target: str) -> list[dict]:
        """One `e5r decompile` call, returning its JSON items."""
        cmd = [str(self._bin), "decompile", str(binary_path), target, "--json"]
        threads = os.environ.get("E5R_THREADS")
        if threads:
            cmd += ["--threads", threads]
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=self.config.binary_timeout_seconds,
        )
        # Exit 1 is "nothing found", which is an empty answer rather than a crash.
        if proc.returncode not in (0, 1):
            raise RuntimeError(f"e5r exit {proc.returncode}: {proc.stderr.strip()[:200]}")
        if not proc.stdout.strip():
            return []
        doc = json.loads(proc.stdout)
        if doc.get("schema") != "e5r/1":
            raise RuntimeError(f"unexpected schema {doc.get('schema')!r}")
        return list(doc.get("items") or [])
