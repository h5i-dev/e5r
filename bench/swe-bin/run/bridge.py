"""MCP (stdio) bridge between a Claude Code session and one swe-bin episode.

Claude Code starts this as its only MCP server. The bridge opens one OpenEnv session on the
swe-bin server (WebSocket, OpenEnv's own MCPToolClient), resets it to the task, and exposes:
  * the environment's tools, unchanged (list_files, read_file, disasm, asm, link, run_tests, ...);
  * `submit`, the environment's step action, which ends the episode.
Every call is appended to LOG_DIR/calls.jsonl. At the deadline, if nothing was submitted, the
bridge submits the episode's current binaries itself. The outcome goes to LOG_DIR/result.json.

The bridge holds no task data: the episode directory, the tests and the artifacts stay behind
the server, which only answers the environment's tools.

  bridge.py --url http://127.0.0.1:8800 --seed N --episode-id ID --log-dir DIR --deadline EPOCH
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import sys
import time

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
sys.path.insert(0, os.path.join(os.environ.get("OPENENV_SRC", os.path.join(SWB, "OpenEnv")), "src"))

import mcp.types as types  # noqa: E402
from mcp.server.lowlevel import Server  # noqa: E402
from mcp.server.stdio import stdio_server  # noqa: E402
from openenv.core.env_server.types import Action  # noqa: E402
from openenv.core.mcp_client import MCPToolClient  # noqa: E402


class Submit(Action):
    submit: list[str]


SUBMIT_SCHEMA = {"type": "object", "properties": {"files": {
    "type": "array", "items": {"type": "string"},
    "description": "the binaries to submit, one per subject (default: the starting file names)"}}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--url", required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--episode-id", required=True)
    ap.add_argument("--log-dir", required=True)
    ap.add_argument("--deadline", type=float, required=True)
    ap.add_argument("--task", required=True, help="the task id the episode must be (checked at reset)")
    a = ap.parse_args()
    os.makedirs(a.log_dir, exist_ok=True)
    calls = open(os.path.join(a.log_dir, "calls.jsonl"), "a")
    server = Server("swebin")
    state = {"env": None, "tools": [], "done": False, "lock": asyncio.Lock(), "t0": time.time()}

    async def env():
        if state["env"] is None:
            c = MCPToolClient(base_url=a.url, message_timeout_s=7200.0,
                              websocket_ping_interval_s=None, websocket_ping_timeout_s=None)
            await c.connect()
            r = await c.reset(seed=a.seed, episode_id=a.episode_id)
            state["reset"] = getattr(r.observation, "message", "")
            got = getattr(r.observation, "task", None)
            with open(os.path.join(a.log_dir, "reset.json"), "w") as fh:
                json.dump({"task": got, "message": state["reset"]}, fh)
            if got != a.task:
                raise RuntimeError(f"seed {a.seed} gave task {got}, not {a.task}: the server's task list differs")
            state["tools"] = await c.list_tools()
            state["env"] = c
        return state["env"]

    async def do_submit(files, auto=False):
        c = await env()
        res = await c.step(Submit(submit=files or []))
        o = res.observation
        out = {"reward": res.reward, "done": res.done, "message": getattr(o, "message", ""),
               "tests": getattr(o, "tests", None), "auto_submitted": auto,
               "wall_s": round(time.time() - state["t0"], 1)}
        with open(os.path.join(a.log_dir, "result.json"), "w") as fh:
            json.dump(out, fh, indent=1)
        state["done"] = True
        return out

    @server.list_tools()
    async def list_tools() -> list[types.Tool]:
        async with state["lock"]:
            await env()
        ts = [types.Tool(name=t.name, description=t.description, inputSchema=t.input_schema) for t in state["tools"]]
        ts.append(types.Tool(name="submit", description="Submit the fixed binary (the environment's step "
                             "action). This ends the episode: the tests run once, and the reward is final.",
                             inputSchema=SUBMIT_SCHEMA))
        return ts

    @server.call_tool()
    async def call_tool(name: str, arguments: dict) -> list[types.TextContent]:
        t = time.time()
        ok = True
        async with state["lock"]:
            try:
                if state["done"]:
                    text = "the episode has ended (submitted)"
                    ok = False
                elif name == "submit":
                    text = json.dumps(await do_submit(arguments.get("files")))
                else:
                    c = await env()
                    r = await c.call_tool(name, **(arguments or {}))
                    text = r if isinstance(r, str) else json.dumps(r)
            except Exception as e:  # tool errors go back to the model as text
                ok = False
                text = f"error: {e}"
        calls.write(json.dumps({"t": round(t - state["t0"], 1), "tool": name, "ok": ok,
                                "args": {k: (v if len(str(v)) < 300 else str(v)[:300] + "...") for k, v in (arguments or {}).items()},
                                "s": round(time.time() - t, 2), "out_bytes": len(text)}) + "\n")
        calls.flush()
        return [types.TextContent(type="text", text=text)]

    async def deadline():
        while time.time() < a.deadline:
            await asyncio.sleep(10)
        async with state["lock"]:
            if not state["done"]:
                await do_submit(None, auto=True)

    async def run():
        async with stdio_server() as (r, w):
            asyncio.get_running_loop().create_task(deadline())
            await server.run(r, w, server.create_initialization_options())

    asyncio.run(run())


if __name__ == "__main__":
    main()
