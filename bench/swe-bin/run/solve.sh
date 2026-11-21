#!/usr/bin/env bash
# solve.sh TASK_ID: one pilot episode of TASK_ID in patch mode, solved by Claude Code (the TUI, in
# tmux session swe-<short id>) with the environment's tools as its only tools.
#
# Isolation (enforced, not asked for in the prompt):
#   --tools ""                built-in tools: none (no Bash, Read, Write, Edit, Glob, Grep, ...)
#   --strict-mcp-config       MCP servers: only the `swebin` bridge of --mcp-config
#   --allowedTools / --disallowedTools / settings deny list, --permission-mode dontAsk
#   cwd                       a fresh empty directory under $SWB/pilot, outside the repository
# The bridge (run/bridge.py) holds one episode; the server keeps the tasks, tests and artifacts.
#
# Env: SWB, PILOT (results dir), MODEL (default claude-opus-4-8), WALL_MIN (default 90),
#      PORT (default 8800).
set -euo pipefail
TASK=$1
SWB=${SWB:-/mnt/scratch/ec2-user/swe-bin}
HERE=$(cd "$(dirname "$0")" && pwd)
BENCH=$(dirname "$HERE")
MODEL=${MODEL:-claude-opus-4-8}
WALL_MIN=${WALL_MIN:-90}
PORT=${PORT:-8800}
PY=$SWB/venv312/bin/python
DATE=${DATE:-$(date -u +%Y-%m-%d)}
RUN=$SWB/pilot/$DATE/$TASK
SHORT=$(echo "$TASK" | sed 's/__/-/; s/[^A-Za-z0-9-]//g' | cut -c1-40)
SESSION=swe-$SHORT

# the server (one for all pilot episodes, patch mode)
if ! curl -fsS --max-time 1 "http://127.0.0.1:$PORT/health" >/dev/null 2>&1; then
  mkdir -p "$SWB/logs"
  nohup /mnt/scratch/ec2-user/target-nc-d/release/swe-bin-env --bind "127.0.0.1:$PORT" --mode patch \
    --max-sessions 8 --idle-timeout-secs 0 --episodes "$SWB/episodes-pilot" \
    --nocompiler /mnt/scratch/ec2-user/target-nc-d/release/nocompiler --bench "$BENCH" \
    > "$SWB/logs/pilot-server.log" 2>&1 &
  for _ in $(seq 1 100); do curl -fsS --max-time 1 "http://127.0.0.1:$PORT/health" >/dev/null 2>&1 && break; sleep 0.2; done
fi

# the seed of the task: its index among the kept tasks, in the order the server loads them
SEED=$($PY - "$BENCH/tasks" "$TASK" <<'EOF'
import json, os, sys
d, t = sys.argv[1], sys.argv[2]
kept = [f[:-5] for f in sorted(os.listdir(d)) if f.endswith(".json") and json.load(open(os.path.join(d, f))).get("status") == "kept"]
print(kept.index(t))
EOF
)

rm -rf "$RUN"; mkdir -p "$RUN/cwd" "$RUN/logs"
START=$(date +%s)
DEADLINE=$((START + WALL_MIN * 60))
cat > "$RUN/mcp.json" <<EOF
{"mcpServers": {"swebin": {"type": "stdio", "command": "$PY",
  "args": ["$HERE/bridge.py", "--url", "http://127.0.0.1:$PORT", "--seed", "$SEED",
           "--episode-id", "pilot-$SHORT", "--log-dir", "$RUN/logs", "--deadline", "$DEADLINE",
           "--task", "$TASK"]}}}
EOF
DENY='"Bash","Read","Write","Edit","Glob","Grep","NotebookEdit","WebFetch","WebSearch","Agent","Task","LSP","Skill"'
cat > "$RUN/settings.json" <<EOF
{"permissions": {"allow": ["mcp__swebin"], "deny": [$DENY]}}
EOF
# the prompt: the committed template with the task's issue text (PROMPT_FILE: the isolation probe)
$PY - "${PROMPT_FILE:-$HERE/prompt.md}" "$SWB/dl/cr.jsonl" "$TASK" > "$RUN/prompt.txt" <<'EOF'
import json, sys
tpl, ds, t = sys.argv[1:4]
row = next(json.loads(l) for l in open(ds) if json.loads(l)["instance_id"] == t)
print(open(tpl).read().replace("{ISSUE}", row["problem_statement"]))
EOF

tmux kill-session -t "$SESSION" 2>/dev/null || true
tmux new-session -d -s "$SESSION" -x 200 -y 50 -c "$RUN/cwd" \
  "claude --model $MODEL --mcp-config $RUN/mcp.json --strict-mcp-config --tools '' \
     --allowedTools mcp__swebin --disallowedTools Bash Read Write Edit Glob Grep NotebookEdit WebFetch WebSearch Agent Task \
     --permission-mode dontAsk --settings $RUN/settings.json; sleep 3600"
# the folder-trust question, then the prompt
for _ in $(seq 1 60); do
  P=$(tmux capture-pane -p -t "$SESSION")
  # "No, exit" is the default answer: choose "Yes, I trust this folder" (the empty cwd)
  if echo "$P" | grep -q "Yes, I trust this folder"; then
    tmux send-keys -t "$SESSION" Down; sleep 0.5; tmux send-keys -t "$SESSION" Enter; sleep 3
  fi
  if echo "$P" | grep -qE "^│ >|^> |\? for shortcuts"; then break; fi
  sleep 1
done
tmux load-buffer -b "p-$SHORT" "$RUN/prompt.txt"
tmux paste-buffer -b "p-$SHORT" -t "$SESSION"
sleep 2; tmux send-keys -t "$SESSION" Enter
echo "$TASK: seed $SEED, tmux $SESSION, run dir $RUN, deadline $(date -u -d @$DEADLINE +%H:%M:%S) UTC"

# wait for the submission (by the agent, or by the bridge at the deadline)
while [ ! -f "$RUN/logs/result.json" ] && [ "$(date +%s)" -lt $((DEADLINE + 900)) ]; do sleep 20; done
END=$(date +%s)
tmux capture-pane -p -t "$SESSION" -S -200 > "$RUN/logs/pane-end.txt" 2>/dev/null || true
tmux kill-session -t "$SESSION" 2>/dev/null || true
# the transcript Claude Code wrote for this cwd
TDIR=$HOME/.claude/projects/$(echo "$RUN/cwd" | sed 's#[^A-Za-z0-9-]#-#g')
TRANSCRIPT=$(ls -t "$TDIR"/*.jsonl 2>/dev/null | head -1 || true)
$PY - "$RUN" "$TASK" "$START" "$END" "$TRANSCRIPT" "$SWB/episodes-pilot/pilot-$SHORT" <<'EOF'
import hashlib, json, os, sys
run, task, s, e, tr, ep = sys.argv[1:7]
res = json.load(open(os.path.join(run, "logs", "result.json"))) if os.path.exists(os.path.join(run, "logs", "result.json")) else None
calls = [json.loads(l) for l in open(os.path.join(run, "logs", "calls.jsonl"))] if os.path.exists(os.path.join(run, "logs", "calls.jsonl")) else []
sub = os.path.join(ep, ".submitted")
shas = [hashlib.sha256(open(os.path.join(sub, f), "rb").read()).hexdigest() for f in sorted(os.listdir(sub))] if os.path.isdir(sub) else []
t = (res or {}).get("tests") or {}
row = {"task": task, "reward": None if res is None else res["reward"],
       "submitted": "none" if res is None else ("auto (deadline)" if res.get("auto_submitted") else "agent"),
       "f2p": f"{t.get('f2p_passed', '?')}/{t.get('f2p', '?')}", "p2p": f"{t.get('p2p_passed', '?')}/{t.get('p2p', '?')}",
       "proof_bonus": "no (check_proof not available)", "wall_s": int(e) - int(s), "tool_calls": len(calls),
       "tools_used": sorted({c["tool"] for c in calls}), "transcript": tr, "submitted_sha256": shas}
json.dump(row, open(os.path.join(run, "row.json"), "w"), indent=1)
print(json.dumps(row))
EOF
