"""Stage 4: scripted episodes without an LLM, over the real OpenEnv protocol.

Starts `swe-bin-env`, then with OpenEnv's own `MCPToolClient` (pinned checkout, WebSocket):
  * patch mode, task T: list the tools, disassemble a function through the `disasm` tool, put
    the GOLD binary in the episode directory (the script does this on the filesystem: it is the
    oracle, not an agent action), submit it: reward 1000, done;
  * the same task, submitting the unchanged base binary: reward 0, done;
  * a step after done is refused.
In scratch mode the starting binary has the removed functions stubbed: the "gold" episode
extracts the gold build's versions of them (swb-elf extract, the oracle) and links them in with
the environment's `link` tool; the "base" episode submits the stubs.

  smoke.py --task jqlang__jq-2650 [--mode patch|scratch]

Environment: OPENENV_SRC (default $SWB/OpenEnv), SWB, NOCOMPILER, SWB_ENV_BIN.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
import urllib.request

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
OPENENV = os.environ.get("OPENENV_SRC", os.path.join(SWB, "OpenEnv"))
sys.path.insert(0, os.path.join(OPENENV, "src"))

from openenv.core.env_server.types import Action  # noqa: E402
from openenv.core.mcp_client import MCPToolClient  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SWB_ELF = os.environ.get("SWB_ELF", "/mnt/scratch/ec2-user/target-nc-d/release/swb-elf")
BENCH = os.path.dirname(HERE)


class Submit(Action):
    submit: list[str]


def kept_tasks():
    names = sorted(f for f in os.listdir(os.path.join(BENCH, "tasks")) if f.endswith(".json"))
    out = []
    for n in names:
        with open(os.path.join(BENCH, "tasks", n)) as fh:
            j = json.load(fh)
        if j["status"] == "kept":
            out.append(j)
    return out


def wait_health(url, proc, log):
    for _ in range(300):
        try:
            urllib.request.urlopen(url + "/health", timeout=0.5)
            return
        except Exception:
            if proc.poll() is not None:
                raise SystemExit("server exited:\n" + open(log).read())
            time.sleep(0.1)
    raise SystemExit("no /health")


def episode(env, seed, eid, put, files, label):
    t0 = time.time()
    r = env.reset(seed=seed, episode_id=eid)
    obs = r.observation
    print(f"[{label}] reset: {getattr(obs, 'message', '')}")
    put()
    res = env.step(Submit(submit=files))
    o = res.observation
    print(f"[{label}] submit: reward={res.reward} done={res.done}")
    print(f"[{label}]   {getattr(o, 'message', '')}")
    print(f"[{label}]   tests: {json.dumps(getattr(o, 'tests', None))[:600]}")
    print(f"[{label}]   {time.time() - t0:.0f}s")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", required=True)
    ap.add_argument("--mode", default="patch", choices=["patch", "scratch"])
    ap.add_argument("--bind", default="127.0.0.1:8791")
    a = ap.parse_args()
    tasks = kept_tasks()
    ids = [t["instance_id"] for t in tasks]
    seed = ids.index(a.task)
    task = tasks[seed]
    subjects = [b["subject"] for b in task["binaries"]]
    files = [os.path.basename(s) + ".elf" for s in subjects]
    episodes = os.path.join(SWB, "episodes-smoke")
    log = os.path.join(SWB, "logs", "smoke-server.log")
    binp = os.environ.get("SWB_ENV_BIN", "/mnt/scratch/ec2-user/target-nc-d/release/swe-bin-env")
    nc = os.environ.get("NOCOMPILER", "/mnt/scratch/ec2-user/target-nc-d/release/nocompiler")
    proc = subprocess.Popen([binp, "--bind", a.bind, "--mode", a.mode, "--episodes", episodes,
                             "--nocompiler", nc, "--bench", BENCH],
                            stdout=open(log, "w"), stderr=subprocess.STDOUT)
    url = f"http://{a.bind}"
    try:
        wait_health(url, proc, log)
        print(f"server: {binp} --mode {a.mode}; task {a.task} is seed {seed} of {len(ids)} kept tasks")
        # a submit runs the tests under qemu, which takes minutes: no 60 s message timeout, and
        # no keepalive pings (the server answers them only between messages)
        client = MCPToolClient(base_url=url, message_timeout_s=3600.0,
                               websocket_ping_interval_s=None, websocket_ping_timeout_s=None)
        with client.sync() as env:
            # the gold binary: reward 1000
            env.reset(seed=seed, episode_id="smoke-gold")
            tools = env.list_tools()
            print(f"[tools] {len(tools)}: {' '.join(t.name for t in tools)}")
            fn = task["binaries"][0]["gold_changes"]["modified"]
            fname = fn[0]["name"] if fn else "main"
            d = env.call_tool("disasm", file=files[0], target=fname)
            out = d["output"] if isinstance(d, dict) else str(d)
            lines = [x for x in out.splitlines() if x.strip()]
            print(f"[tools] disasm {files[0]} {fname}: {len(out)} bytes; exit {d.get('exit') if isinstance(d, dict) else '?'}")
            for x in lines[:3]:
                print(f"[tools]   | {x[:150]}")
            try:
                env.call_tool("read_file", file="../x")
                print("[tools] read_file ../x: NOT refused (bug)")
            except RuntimeError as e:
                print(f"[tools] read_file ../x refused: {str(e)[:120]}")

            def put_gold():
                ep = os.path.join(episodes, "smoke-gold")
                for b, f in zip(task["binaries"], files):
                    if a.mode == "patch":
                        shutil.copy(os.path.join(SWB, b["gold"]["path"]), os.path.join(ep, f))
                        continue
                    # scratch: the gold build's versions of the removed functions, as an object
                    # (the oracle's step), then linked by the environment's own `link` tool
                    names = b["scratch"]["removes"] + b["scratch"].get("new_functions", [])
                    if not names:
                        continue
                    obj = os.path.join(ep, f"gold-{f}.o")
                    subprocess.run([SWB_ELF, "extract", os.path.join(SWB, b["gold"]["path"]), obj] + names, check=True,
                                   stdout=subprocess.DEVNULL)
                    r = env.call_tool("link", binary=f, object=os.path.basename(obj), out=f)
                    print(f"[gold] link {os.path.basename(obj)} into {f}: {r}")

            gold = episode(env, seed, "smoke-gold", put_gold, files, "gold")
            try:
                env.step(Submit(submit=files))
                print("[after done] step accepted (bug)")
            except Exception as e:  # the server answers with an error frame
                print(f"[after done] refused: {str(e)[:160]}")
            base = episode(env, seed, "smoke-base", lambda: None, files, "base")
        # the wire carries the reward in units: Reward::Milli(1000) is 1.0
        ok = gold.reward == 1.0 and gold.done and base.reward == 0.0 and base.done
        print("SMOKE", "PASS" if ok else "FAIL", f"gold={gold.reward} ({gold.reward * 1000:.0f} milli) base={base.reward}")
        sys.exit(0 if ok else 1)
    finally:
        proc.terminate()
        proc.wait(timeout=10)


if __name__ == "__main__":
    main()
