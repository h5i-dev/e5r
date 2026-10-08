"use strict";
const $ = (id) => document.getElementById(id);
const state = {
  project: null,
  board: { tasks: [] },
  functions: [],
  selected: null,
  pane: "decompile",
  editing: null,
  request: 0,
  history: [],
  code: "",
  boardStamp: "",
  functionLimit: 400,
};
const labels = {
  planned: "Planned",
  active: "Active",
  blocked: "Blocked",
  review: "Review",
  done: "Done",
};
const blank = () => ({
  title: "",
  description: "",
  state: "planned",
  priority: "normal",
  owner: "",
  next: "",
  blocker: "",
  evidence: [],
  depends_on: [],
});
function el(tag, text, className) {
  const e = document.createElement(tag);
  if (text !== undefined) e.textContent = text;
  if (className) e.className = className;
  return e;
}
function clear(node) {
  node.replaceChildren();
}
function tag(value) {
  return el("span", labels[value] || value, `state ${value}`);
}
function message(node, title, detail) {
  clear(node);
  const e = el("div", undefined, "empty");
  e.append(el("strong", title));
  if (detail) e.append(el("span", detail));
  node.append(e);
}
function shellQuote(text) {
  return "'" + text.replaceAll("'", "'\\''") + "'";
}
async function api(path, body) {
  const response = await fetch(
    path,
    body === undefined
      ? {}
      : {
          method: "POST",
          headers: {
            "Content-Type": "application/json",
            "X-E5R-Client": "dashboard",
          },
          body: JSON.stringify(body),
        },
  );
  const data = await response.json();
  if (!response.ok) {
    const error = new Error(
      data.error || `Request failed (${response.status})`,
    );
    error.status = response.status;
    throw error;
  }
  return data;
}
function error(text) {
  $("error").textContent = text;
  $("error").hidden = !text;
}
async function copy(text, button) {
  try {
    await navigator.clipboard.writeText(text);
    const original = button.textContent;
    button.textContent = "Copied";
    setTimeout(() => (button.textContent = original), 1200);
  } catch {
    error("Clipboard unavailable. Select and copy the displayed text.");
  }
}
function view(name) {
  $("overview").hidden = name !== "overview";
  $("workspace").hidden = name !== "workspace";
  document
    .querySelectorAll("[data-view]")
    .forEach((b) => b.classList.toggle("selected", b.dataset.view === name));
  $("view-title").textContent =
    name === "overview" ? "Project overview" : "Decompiler workspace";
  if (name === "workspace" && !state.functions.length) loadFunctions();
}
function route() {
  const parts = location.hash.slice(1).split("/");
  view(parts[0] === "workspace" ? "workspace" : "overview");
  if (
    parts[0] === "workspace" &&
    parts[1] &&
    /^0x[0-9a-f]+$/i.test(parts[1]) &&
    state.functions.length
  ) {
    const f = state.functions.find((f) => f.addr === parts[1]);
    if (f && f.addr !== state.selected?.addr) selectFunction(f, false);
  }
}
function rowButton(row, reason) {
  const button = el("button", undefined, "work-row");
  button.type = "button";
  const title = el("div", undefined, "work-row-title");
  const text = el("span");
  text.append(
    el("span", row.task.id, "id"),
    document.createTextNode(row.task.content.title),
  );
  title.append(text, tag(row.task.content.state));
  button.append(
    title,
    el(
      "div",
      reason ||
        row.task.content.next ||
        "Add a next action to make this easy to hand off.",
      "work-row-sub",
    ),
  );
  button.addEventListener("click", () => openTask(row.task));
  return button;
}
function renderBoard() {
  const tasks = state.board.tasks,
    open = tasks.filter((r) => r.task.content.state !== "done"),
    attention = tasks.filter((r) => r.attention),
    ready = tasks.filter((r) => r.ready),
    active = tasks.filter((r) => r.task.content.state === "active");
  $("headline").textContent = attention.length
    ? `${attention.length} ${attention.length === 1 ? "item needs" : "items need"} attention.`
    : open.length
      ? "The next step is clear."
      : "A clear desk. A new investigation.";
  $("headline-sub").textContent = attention.length
    ? "Blockers and review requests come first. Each item says what is needed."
    : open.length
      ? `${active.length} active · ${ready.length} ready to pick up. Keep owners and next actions current for a smooth handoff.`
      : "Start with an outcome, assign an owner, and record the evidence as you go.";
  clear($("counts"));
  for (const [n, label, tone] of [
    [attention.length, "need attention", "attention"],
    [active.length, "active", ""],
    [ready.length, "ready", ""],
  ]) {
    const e = el("div", undefined, `count ${tone}`);
    e.append(el("b", String(n)), el("span", label));
    $("counts").append(e);
  }
  $("attention-count").textContent = String(attention.length);
  $("ready-count").textContent = String(ready.length);
  clear($("attention"));
  clear($("ready"));
  attention
    .slice(0, 6)
    .forEach((r) => $("attention").append(rowButton(r, r.attention)));
  ready.slice(0, 6).forEach((r) => $("ready").append(rowButton(r)));
  if (!attention.length)
    message(
      $("attention"),
      "Nothing is waiting on you.",
      "No blocked task or result awaiting review.",
    );
  if (!ready.length)
    message(
      $("ready"),
      open.length ? "No task ready to claim." : "Start the first task.",
      open.length
        ? "Active work, blockers and prerequisites are listed below."
        : "Use “New task” to capture the next investigation.",
    );
  if (attention.length > 6)
    $("attention").append(
      el("p", `${attention.length - 6} more in Project work below.`, "empty"),
    );
  if (ready.length > 6)
    $("ready").append(
      el("p", `${ready.length - 6} more in Project work below.`, "empty"),
    );
  renderTasks();
  renderRelated();
}
function renderTasks() {
  const q = $("task-search").value.toLowerCase(),
    filter = $("task-filter").value;
  const tasks = state.board.tasks.filter(
    (r) =>
      (filter === "all" ||
        (filter === "open" && r.task.content.state !== "done") ||
        r.task.content.state === filter) &&
      [
        r.task.id,
        r.task.content.title,
        r.task.content.owner,
        r.task.content.next,
      ]
        .join(" ")
        .toLowerCase()
        .includes(q),
  );
  clear($("task-rows"));
  for (const row of tasks) {
    const t = row.task,
      d = t.content,
      tr = el("tr"),
      outcome = el("td"),
      button = el("button", d.title, "task-open");
    button.type = "button";
    button.onclick = () => openTask(t);
    outcome.append(
      el("span", t.id, "id"),
      button,
      el(
        "span",
        `${d.priority} priority · revision ${t.revision}`,
        "task-note",
      ),
    );
    const status = el("td");
    status.append(tag(d.state));
    if (row.waiting_on.length)
      status.append(
        el("span", `Waiting on ${row.waiting_on.join(", ")}`, "task-note"),
      );
    tr.append(
      outcome,
      status,
      el("td", d.owner || "Unassigned", "muted"),
      el("td", row.attention || d.next || "No next action recorded"),
    );
    $("task-rows").append(tr);
  }
  $("task-empty").hidden = !!tasks.length;
  $("task-empty").textContent = state.board.tasks.length
    ? "No tasks match this view."
    : "No tasks yet. Create an outcome for a person or agent to work toward.";
}
async function refreshTasks() {
  try {
    const board = await api("/api/tasks"),
      stamp = JSON.stringify(board);
    state.board = board;
    if (stamp !== state.boardStamp) {
      state.boardStamp = stamp;
      renderBoard();
    }
    $("sync").textContent = "Tasks up to date";
    error("");
  } catch (e) {
    $("sync").textContent = "Tasks unavailable";
    error(`Could not refresh tasks: ${e.message}`);
  }
}
function openTask(task = null, content = null) {
  state.editing = task;
  const d = content || task?.content || blank(),
    form = $("task-form");
  for (const key of [
    "title",
    "description",
    "state",
    "priority",
    "owner",
    "next",
    "blocker",
  ])
    form.elements[key].value = d[key];
  form.elements.evidence.value = d.evidence.join("\n");
  form.elements.depends_on.value = d.depends_on.join(", ");
  form.elements.author.value =
    localStorage.getItem("e5r.writer") || state.project?.author || "human";
  $("edit-id").textContent = task
    ? `${task.id} · REVISION ${task.revision}`
    : "NEW TASK";
  $("edit-heading").textContent = task
    ? "Keep the next step clear"
    : "Define the next outcome";
  $("revision-note").textContent = task
    ? "Stale edits are refused. Task history is retained."
    : "Saved beside the project; shared with agents.";
  $("form-error").hidden = true;
  $("reload-task").hidden = true;
  $("history").hidden = !task?.history.length;
  clear($("history-items"));
  for (const h of [...(task?.history || [])].reverse()) {
    const div = el("div", undefined, "history-row");
    div.append(
      el("strong", `${h.author} · ${new Date(h.at * 1000).toLocaleString()}`),
      el("div", `${labels[h.previous.state]} · ${h.previous.title}`),
      el("div", h.previous.next || "No next action"),
    );
    $("history-items").append(div);
  }
  blockerToggle();
  if (!$("task-dialog").open) $("task-dialog").showModal();
  form.elements.title.focus();
}
function blockerToggle() {
  const blocked = $("task-form").elements.state.value === "blocked";
  $("blocker-label").hidden = !blocked;
  $("task-form").elements.blocker.required = blocked;
}
async function saveTask(event) {
  event.preventDefault();
  const form = $("task-form"),
    content = blank();
  for (const key of [
    "title",
    "description",
    "state",
    "priority",
    "owner",
    "next",
    "blocker",
  ])
    content[key] = form.elements[key].value.trim();
  if (content.state !== "blocked") content.blocker = "";
  content.evidence = form.elements.evidence.value
    .split("\n")
    .map((s) => s.trim())
    .filter(Boolean);
  content.depends_on = form.elements.depends_on.value
    .split(/[\s,]+/)
    .filter(Boolean);
  const author = form.elements.author.value.trim();
  $("save-task").disabled = true;
  $("form-error").hidden = true;
  try {
    await api(state.editing ? `/api/tasks/${state.editing.id}` : "/api/tasks", {
      content,
      author,
      revision: state.editing?.revision ?? null,
    });
    localStorage.setItem("e5r.writer", author);
    $("task-dialog").close();
    await refreshTasks();
  } catch (e) {
    $("form-error").textContent = e.message;
    $("form-error").hidden = false;
    $("reload-task").hidden = e.status !== 409;
  } finally {
    $("save-task").disabled = false;
  }
}
async function loadFunctions() {
  $("function-count").textContent = "Loading…";
  try {
    const data = await api("/api/functions");
    state.functions = data.items;
    renderFunctions();
    route();
  } catch (e) {
    message($("functions"), "Could not load functions.", e.message);
    $("function-count").textContent = "Error";
  }
}
function renderFunctions() {
  const query = $("function-search").value.toLowerCase();
  const items = state.functions.filter((f) =>
    `${f.name} ${f.addr}`.toLowerCase().includes(query),
  );
  clear($("functions"));
  $("function-count").textContent =
    `${items.length.toLocaleString()} / ${state.functions.length.toLocaleString()}`;
  for (const f of items.slice(0, state.functionLimit)) {
    const b = el("button", undefined, "function-row");
    b.classList.toggle("selected", f.addr === state.selected?.addr);
    b.setAttribute("aria-current", String(f.addr === state.selected?.addr));
    b.title = f.name;
    b.append(
      el("strong", f.name),
      el(
        "small",
        `${f.addr} · ${f.insns} insns${f.complete ? "" : " · incomplete"}`,
      ),
    );
    b.onclick = () => selectFunction(f);
    $("functions").append(b);
  }
  if (items.length > state.functionLimit) {
    const more = el(
      "button",
      `Show next ${Math.min(400, items.length - state.functionLimit)} functions`,
      "work-row",
    );
    more.onclick = () => {
      state.functionLimit += 400;
      renderFunctions();
    };
    $("functions").append(more);
  }
  if (!items.length)
    message(
      $("functions"),
      "No functions found.",
      query
        ? "Try a name or address."
        : "This binary has no recovered functions.",
    );
}
function selectFunction(f, push = true) {
  if (push && state.selected && state.selected.addr !== f.addr)
    state.history.push(state.selected.addr);
  state.selected = f;
  state.code = "";
  $("back").disabled = !state.history.length;
  $("function-name").textContent = f.name;
  $("function-address").textContent = f.addr;
  $("task-function").disabled = false;
  $("copy-code").disabled = true;
  history.replaceState(null, "", `#workspace/${f.addr}`);
  view("workspace");
  renderFunctions();
  renderContext();
  $("variables-section").hidden = true;
  renderRelated();
  loadPane();
}
function renderContext() {
  const f = state.selected;
  clear($("function-context"));
  const dl = el("dl");
  for (const [name, value] of [
    ["Boundary strength", f.strength],
    ["Evidence", f.evidence.join(", ") || "None reported"],
    ["Coverage", f.complete ? "Complete" : "Incomplete — " + f.halt],
    ["Shape", `${f.blocks} blocks · ${f.insns} instructions`],
    ["Indirect control flow", f.indirect ? "Present" : "None reported"],
  ])
    dl.append(el("dt", name), el("dd", value));
  $("function-context").append(dl);
}
function renderRelated() {
  if (!state.selected) return;
  const addr = state.selected.addr;
  const tasks = state.board.tasks.filter((r) =>
    r.task.content.evidence.some((e) => e === `function:${addr}` || e === addr),
  );
  clear($("related-work"));
  tasks.forEach((r) =>
    $("related-work").append(rowButton(r, r.attention || r.task.content.next)),
  );
  if (!tasks.length)
    $("related-work").textContent =
      "No task linked yet. “Task here” preserves this function as evidence.";
}
function syntaxLine(line, known) {
  const container = el("span", undefined, "line-source");
  const token =
    /\/\/.*$|\/\*.*?\*\/|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|\b(?:0x[0-9a-fA-F]+|\d+)\b|\b[a-zA-Z_][\w]*\b/g;
  let position = 0;
  for (const match of line.matchAll(token)) {
    container.append(
      document.createTextNode(line.slice(position, match.index)),
    );
    const word = match[0];
    let style = "";
    if (word.startsWith("//") || word.startsWith("/*")) style = "comment";
    else if (word.startsWith('"') || word.startsWith("'")) style = "string";
    else if (/^\d/.test(word)) style = "number";
    else if (
      /^(if|else|for|while|do|return|switch|case|default|goto|break|continue|void|int|char|unsigned|signed|long|short|struct|const|static|uint\d+_t|int\d+_t)$/.test(
        word,
      )
    )
      style = "keyword";
    const target = known.get(word);
    if (target) {
      const link = el("a", word, "call");
      link.href = `#workspace/${target.addr}`;
      link.onclick = (e) => {
        e.preventDefault();
        selectFunction(target);
      };
      container.append(link);
    } else container.append(el("span", word, style));
    position = match.index + word.length;
  }
  container.append(document.createTextNode(line.slice(position)));
  return container;
}
function renderCode(code) {
  state.code = code;
  clear($("code"));
  const known = new Map(
    state.functions.flatMap((f) => [
      [f.name, f],
      [f.addr, f],
    ]),
  );
  code.split("\n").forEach((line, i) => {
    const e = el("div", undefined, "code-line");
    e.append(el("span", String(i + 1), "line-number"), syntaxLine(line, known));
    $("code").append(e);
  });
  $("copy-code").disabled = !code;
}
function renderVariables(variables) {
  clear($("variables"));
  $("variables-section").hidden = !variables?.length;
  const dl = el("dl");
  for (const v of variables || [])
    dl.append(
      el("dt", `${v.role} · ${v.storage}`),
      el("dd", `${v.type} ${v.name}`),
    );
  $("variables").append(dl);
}
function renderReferences(data) {
  clear($("code"));
  const rows = data.items || [];
  if (!rows.length) {
    message(
      $("code"),
      "No incoming references reported.",
      "This is the analysis result for this startup snapshot.",
    );
    return;
  }
  const table = el("table", undefined, "references"),
    head = el("thead"),
    tr = el("tr");
  for (const k of Object.keys(rows[0])) tr.append(el("th", k));
  head.append(tr);
  table.append(head);
  const body = el("tbody");
  for (const r of rows) {
    const tr = el("tr");
    for (const [k, v] of Object.entries(r)) {
      const td = el("td"),
        f = state.functions.find(
          (f) =>
            f.addr === String(v) || (k === "from_function" && f.name === v),
        );
      if (f) {
        const b = el("button", String(v), "task-open");
        b.onclick = () => selectFunction(f);
        td.append(b);
      } else
        td.textContent =
          typeof v === "object" ? JSON.stringify(v) : String(v ?? "");
      tr.append(td);
    }
    body.append(tr);
  }
  table.append(body);
  $("code").append(table);
  state.code = JSON.stringify(data, null, 2);
  $("copy-code").disabled = false;
}
async function loadPane() {
  if (!state.selected) return;
  const serial = ++state.request,
    f = state.selected,
    pane = state.pane;
  document
    .querySelectorAll("[data-pane]")
    .forEach((b) =>
      b.setAttribute("aria-selected", String(b.dataset.pane === pane)),
    );
  $("quality").className = "quality";
  $("quality").textContent =
    `Loading ${pane === "decompile" ? "pseudocode" : pane === "disas" ? "disassembly" : "references"}…`;
  message(
    $("code"),
    "Reading the function…",
    "Results come directly from the e5r analysis engine.",
  );
  $("copy-code").disabled = true;
  const command =
    pane === "disas" ? "disas" : pane === "xrefs" ? "xrefs" : "decompile";
  const options = [
    state.project.log ? "--db " + shellQuote(state.project.log) : "",
    state.project.base ? "--base " + state.project.base : "",
    state.project.arch ? "--arch " + shellQuote(state.project.arch) : "",
    state.project.no_scan ? "--no-scan" : "",
    state.project.threads !== null ? "--threads " + state.project.threads : "",
  ]
    .filter(Boolean)
    .join(" ");
  $("analysis-command").textContent =
    `e5r ${command} ${shellQuote(state.project.binary)} ${f.addr}${options ? " " + options : ""}${pane === "disas" ? " --bytes" : ""}`;
  $("copy-analysis").disabled = false;
  try {
    const data = await api(`/api/${pane}/${f.addr}`);
    if (serial !== state.request) return;
    if (pane === "decompile") {
      const d = data.items?.[0];
      if (!d) throw new Error("No decompiler result for this function.");
      const warnings = [];
      if (!f.complete) warnings.push(`Incomplete control flow: ${f.halt}`);
      if (d.unmodelled) warnings.push(`${d.unmodelled} unmodelled operations`);
      if (d.conflicts.length) warnings.push(...d.conflicts);
      $("quality").textContent = warnings.length
        ? warnings.join(" · ")
        : `${f.strength} boundary · ${d.locals} locals · ${d.gotos} gotos${d.asserted ? " · asserted signature" : ""} · Pseudocode is an analysis result.`;
      $("quality").classList.toggle("warning", !!warnings.length);
      renderCode(d.code);
      renderVariables(d.variables);
    } else if (pane === "disas") {
      // CLI disassembly JSON groups instructions under functions.
      const groups = data.items || [];
      const lines = [];
      for (const group of groups) {
        for (const insn of group.insns || []) {
          lines.push(`${insn.addr}  ${insn.text}`);
        }
      }
      if (!lines.length) renderCode(JSON.stringify(data, null, 2));
      else renderCode(lines.join("\n"));
      $("quality").textContent =
        `${f.insns} instructions · ${f.strength} boundary · ${f.complete ? "Complete" : "Incomplete: " + f.halt}`;
    } else {
      renderReferences(data);
      $("quality").textContent =
        "Incoming references reported by e5r. Known function addresses open their function.";
    }
  } catch (e) {
    if (serial !== state.request) return;
    $("quality").textContent = "Output unavailable";
    message($("code"), "Could not show this function.", e.message);
  }
}
for (const b of document.querySelectorAll("[data-view]"))
  b.onclick = () => {
    location.hash = b.dataset.view;
    route();
  };
for (const b of document.querySelectorAll("[data-pane]"))
  b.onclick = () => {
    state.pane = b.dataset.pane;
    loadPane();
  };
$("new-task").onclick = () => openTask();
$("refresh").onclick = refreshTasks;
$("close-dialog").onclick = () => $("task-dialog").close();
$("task-form").onsubmit = saveTask;
$("task-form").elements.state.onchange = blockerToggle;
$("reload-task").onclick = async () => {
  const id = state.editing?.id;
  await refreshTasks();
  const task = state.board.tasks.find((r) => r.task.id === id)?.task;
  if (task) openTask(task);
};
$("task-search").oninput = renderTasks;
$("task-filter").onchange = renderTasks;
$("function-search").oninput = () => {
  state.functionLimit = 400;
  renderFunctions();
};
$("copy-agent").onclick = () =>
  copy($("agent-command").textContent, $("copy-agent"));
$("copy-analysis").onclick = () =>
  copy($("analysis-command").textContent, $("copy-analysis"));
$("wrap-code").onchange = () => {
  $("code").classList.toggle("wrap", $("wrap-code").checked);
  localStorage.setItem("e5r.wrap", String($("wrap-code").checked));
};
$("wrap-code").checked = localStorage.getItem("e5r.wrap") !== "false";
$("code").classList.toggle("wrap", $("wrap-code").checked);
$("copy-code").onclick = () => copy(state.code, $("copy-code"));
$("task-function").onclick = () => {
  const d = blank();
  d.title = `Investigate ${state.selected.name}`;
  d.evidence = [
    `function:${state.selected.addr}`,
    $("analysis-command").textContent,
  ];
  openTask(null, d);
};
$("back").onclick = () => {
  const addr = state.history.pop(),
    f = state.functions.find((f) => f.addr === addr);
  if (f) selectFunction(f, false);
};
window.addEventListener("hashchange", route);
window.addEventListener("keydown", (e) => {
  if (
    e.key === "/" &&
    !$("workspace").hidden &&
    !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName) &&
    !$("task-dialog").open
  ) {
    e.preventDefault();
    $("function-search").focus();
  }
});
async function boot() {
  try {
    state.project = await api("/api/project");
    const name = state.project.project.split("/").pop();
    $("project-name").textContent = name;
    document.title = `${name} · e5r`;
    $("binary-name").textContent = state.project.binary;
    $("agent-command").textContent =
      `e5r project task ${shellQuote(state.project.project)} list --json`;
    renderBoard();
    await refreshTasks();
    route();
    setInterval(refreshTasks, 5000);
  } catch (e) {
    error(`Could not open project: ${e.message}`);
    $("sync").textContent = "Unavailable";
  }
}
boot();
