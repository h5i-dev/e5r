#!/usr/bin/env python3
"""Hold the benchmark numbers to a recorded budget.

A benchmark nobody reruns is a number that rots, so the numbers in
``scripts/bench-budget.json`` are data this script checks rather than prose
somebody reads. It is the same shape as the ratchets elsewhere in this
repository: **a ceiling that only comes down** for wall time and peak memory,
and **a floor that only rises** for recall.

    scripts/check-bench-budget.py bench-tools.json                      # G8
    scripts/check-bench-budget.py bench-tools.json --portable-only --no-timing
    scripts/check-bench-budget.py bench-tools.json --update    # move the ratchet

The budget has two halves, and they are checkable in different places.

**What the analysis found is deterministic.** Recall against the symbol table
and the count of entries no symbol names are the same on any machine, any
thread count and any build profile, so they are checked everywhere. Either one
differing from the recorded value fails, in both directions: below the recall
floor is a regression, and above it is a floor that has stopped catching the
regression that would take it back. A baseline that moves without a reviewer
seeing it is not a baseline, so moving it takes ``--update`` and a commit.

**What it cost is not.** Wall time and peak memory belong to one machine, one
build profile and whatever else that machine was doing. The ceilings here were
recorded from a release build on the machine named in the file, and a dev-profile
build on a CI runner will blow through every one of them for reasons that have
nothing to do with a regression. So ``--no-timing`` drops that half, and a CI
job that cannot reproduce the recording machine uses it. Each ceiling carries
stated headroom over the measurement that set it, because load moves wall time
in one direction only.

Time and memory improvements are reported rather than failed: noise moves them
both ways, and a ceiling that ratchets itself down on a lucky run becomes a
ceiling that fails on an ordinary one. Lower them with ``--update`` when a
change is meant to have made them lower.

Entries measured on system libraries are marked ``portable: false``: this
machine's libc is not another machine's, so a CI runner checks only the
fixtures, which are built from sources in this repository.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

BUDGET = Path(__file__).resolve().parent / "bench-budget.json"

# Headroom over the measurement that set a ceiling. The machine these numbers
# were recorded on runs other work, so wall time varies by a lot and the gate
# has to be loose enough that a busy afternoon is not a regression; 2x is a
# large regression by any reading and is still caught. Peak resident memory
# barely varies, so it gets much less. The measurement that set each ceiling is
# recorded beside it, which is the number to compare against when the question
# is "did this change make it slower" rather than "is it still acceptable".
TIME_HEADROOM = 2.00
MEMORY_HEADROOM = 1.15

# /usr/bin/time reports hundredths of a second. Below a few of those, the
# measurement is the timer rather than the tool, so no ceiling is placed on it
# and no headroom is reported against it.
TIMER_RESOLUTION = 0.02

# The most any speedup floor claims, however large the measured ratio was.
SPEEDUP_FLOOR_CAP = 10.0


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def measured_rows(results: dict) -> dict[str, dict]:
    """The r12e measurement per binary, keyed by binary name."""
    rows = {}
    for row in results["results"]:
        tool = row["tools"].get("r12e")
        if tool and tool.get("ran"):
            rows[row["binary"]] = {
                "seconds": tool["seconds"],
                "peak_mb": round(tool["peak_kb"] / 1024, 1),
                "recall": tool["recall"],
                "extra": tool["extra"],
                "functions": tool["counted"],
                "oracle": row["oracle"],
                "path": row["path"],
            }
    return rows


def ratios(results: dict) -> dict[str, dict[str, float]]:
    """r12e's wall time as a fraction of each other tool's, per binary."""
    out = {}
    for row in results["results"]:
        ours = row["tools"].get("r12e")
        # A ratio against a time at the timer's resolution is arithmetic on
        # noise, so the small fixtures contribute no speedup floor.
        if not ours or not ours.get("ran"):
            continue
        if not ours["seconds"] or ours["seconds"] < TIMER_RESOLUTION:
            continue
        speed = {}
        for other in ("rizin", "ghidra"):
            theirs = row["tools"].get(other)
            if theirs and theirs.get("ran") and theirs["seconds"]:
                speed[other] = round(theirs["seconds"] / ours["seconds"], 2)
        if speed:
            out[row["binary"]] = speed
    return out


def check(
    budget: dict, results: dict, portable_only: bool, timing: bool
) -> tuple[list[str], list[str]]:
    failures: list[str] = []
    notes: list[str] = []
    rows = measured_rows(results)
    speeds = ratios(results)

    for name, entry in budget["binaries"].items():
        if portable_only and not entry.get("portable", False):
            continue
        got = rows.get(name)
        if got is None:
            notes.append(f"{name}: not in this run, not checked")
            continue

        if not timing:
            pass
        elif True:
            failures.extend(timing_breaches(name, entry, got, notes))

        floor = entry.get("recall_floor")
        if floor is not None and got["recall"] is not None:
            if got["recall"] < floor:
                failures.append(
                    f"{name}: recall {got['recall'] * 100:.2f}% below the "
                    f"{floor * 100:.2f}% floor"
                )
            elif got["recall"] > floor:
                failures.append(
                    f"{name}: recall {got['recall'] * 100:.2f}% above the "
                    f"{floor * 100:.2f}% floor; rerun with --update and commit "
                    "the new floor"
                )

        ceiling = entry.get("extra_ceiling")
        if ceiling is not None and got["extra"] != ceiling:
            direction = "above" if got["extra"] > ceiling else "below"
            tail = "" if got["extra"] > ceiling else "; rerun with --update"
            failures.append(
                f"{name}: {got['extra']} entries named by no symbol, {direction} "
                f"the ceiling of {ceiling}{tail}"
            )

    for name, floor in budget.get("speedup_floor", {}).items():
        if portable_only or not timing:
            continue
        got = speeds.get(name)
        if got is None:
            notes.append(f"{name}: no other tool ran, speedup not checked")
            continue
        for tool, want in floor.items():
            have = got.get(tool)
            if have is None:
                notes.append(f"{name}: {tool} did not run, speedup not checked")
            elif have < want:
                failures.append(
                    f"{name}: {have:.2f}x faster than {tool}, below the {want:.2f}x floor"
                )
    return failures, notes


def timing_breaches(name: str, entry: dict, got: dict, notes: list[str]) -> list[str]:
    """Wall time and peak memory against their ceilings."""
    failures: list[str] = []
    ceiling = entry["seconds_ceiling"]
    if got["seconds"] > ceiling:
        failures.append(
            f"{name}: {got['seconds']:.3f}s over the {ceiling:.3f}s ceiling"
        )
    elif ceiling > TIMER_RESOLUTION and got["seconds"] * TIME_HEADROOM < ceiling * 0.98:
        notes.append(
            f"{name}: {got['seconds']:.3f}s, well under the {ceiling:.3f}s ceiling"
        )
    ceiling = entry["peak_mb_ceiling"]
    if got["peak_mb"] > ceiling:
        failures.append(
            f"{name}: {got['peak_mb']:.1f} MB over the {ceiling:.1f} MB ceiling"
        )
    elif got["peak_mb"] * MEMORY_HEADROOM < ceiling * 0.98:
        notes.append(
            f"{name}: {got['peak_mb']:.1f} MB, well under the {ceiling:.1f} MB ceiling"
        )
    return failures


def update(budget: dict, results: dict) -> dict:
    rows = measured_rows(results)
    speeds = ratios(results)
    budget["measured_on"] = results.get("when")
    # Which machine the cost half of this budget belongs to. Recorded rather
    # than assumed: the ceilings are meaningless anywhere else.
    budget["machine"] = results.get("machine")
    budget["versions"] = results.get("versions", {})
    budget["loadavg_when_measured"] = results.get("loadavg")
    for name, got in rows.items():
        # A fixture is built from sources in this repository and is the same
        # bytes anywhere; this machine's libc is not another machine's.
        entry = budget["binaries"].setdefault(name, {})
        entry["portable"] = got["path"].startswith("fixtures/")
        entry["measured_seconds"] = got["seconds"]
        entry["measured_peak_mb"] = got["peak_mb"]
        entry["seconds_ceiling"] = round(
            max(got["seconds"] * TIME_HEADROOM, TIMER_RESOLUTION), 3
        )
        entry["peak_mb_ceiling"] = round(got["peak_mb"] * MEMORY_HEADROOM, 1)
        entry["functions"] = got["functions"]
        entry["extra_ceiling"] = got["extra"]
        entry["oracle"] = got["oracle"]
        if got["recall"] is not None:
            entry["recall_floor"] = got["recall"]
    # The speedup floor is deliberately slack, and capped. It exists to catch
    # r12e losing a standing advantage, not to bet that another tool will never
    # get faster: rizin takes twelve minutes on libstdc++ here, and pinning a
    # floor near that ratio would fail the day rizin fixes it, which is not our
    # regression. An order of magnitude is the most this claims.
    budget["speedup_floor"] = {
        name: {tool: round(min(value * 0.6, SPEEDUP_FLOOR_CAP), 2) for tool, value in got.items()}
        for name, got in speeds.items()
    }
    return budget


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("results", type=Path, help="JSON from scripts/compare-tools.sh")
    ap.add_argument("--budget", type=Path, default=BUDGET)
    ap.add_argument("--portable-only", action="store_true", help="skip system binaries")
    ap.add_argument(
        "--no-timing",
        action="store_true",
        help="check only what the analysis found, not what it cost",
    )
    ap.add_argument("--update", action="store_true", help="record this run as the budget")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    results = load(args.results)
    if args.update:
        budget = load(args.budget) if args.budget.exists() else {"binaries": {}}
        args.budget.write_text(json.dumps(update(budget, results), indent=2) + "\n")
        print(f"budget rewritten from {args.results}: {args.budget}")
        return 0

    if not args.budget.exists():
        print(f"no budget at {args.budget}; record one with --update", file=sys.stderr)
        return 2

    failures, notes = check(
        load(args.budget), results, args.portable_only, not args.no_timing
    )
    if notes and not args.quiet:
        for note in notes:
            print(f"note: {note}")
    for failure in failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    if failures:
        print(
            f"\n{len(failures)} breach(es) of scripts/bench-budget.json. "
            "A deliberate change moves the budget with --update, in the same "
            "commit, so a reviewer sees the number move.",
            file=sys.stderr,
        )
        return 1
    print("benchmark budget: green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
