"use strict";
const base = location.pathname.startsWith("/p/")
  ? location.pathname.replace(/\/$/, "")
  : "";
const $ = (id) => document.getElementById(id);
const state = {
  project: null,
  board: { tasks: [] },
  functions: [],
  selected: null,
  pane: "decompile",
  currentTask: null,
  recordStamp: "",
  records: null,
  recordsError: "",
  request: 0,
  contextRequest: 0,
  context: null,
  contextError: "",
  contextPromise: null,
  referenceDirection: "incoming",
  instructionTarget: null,
  history: [],
  future: [],
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
async function api(path) {
  const response = await fetch(base + path);
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
  if (parts[0] === "task" && parts[1]) {
    const task = state.board.tasks.find(
      (row) => row.task.id === parts[1],
    )?.task;
    if (task && !$("task-dialog").open) openTask(task);
  }
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
    const e = el("div", undefined, `count ${n ? tone : ""}`);
    e.append(el("b", String(n)), el("span", label));
    $("counts").append(e);
  }
  $("attention-count").textContent = String(attention.length);
  $("attention").closest(".attention-panel").classList.toggle("quiet", !attention.length);
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
        : "Ask an agent to capture the next investigation.",
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
    if ($("task-dialog").open && state.currentTask) {
      const latest = board.tasks.find(r => r.task.id === state.currentTask.id)?.task;
      if (latest && latest.revision !== state.currentTask.revision) openTask(latest);
    }
    if (stamp !== state.boardStamp) {
      state.boardStamp = stamp;
      renderBoard();
    }
    $("sync").textContent = "Tasks up to date";
    if (!state.project?.binary_error) error("");
  } catch (e) {
    $("sync").textContent = "Tasks unavailable";
    error(`Could not refresh tasks: ${e.message}`);
  }
}
function openTask(task) {
  state.currentTask = task;
  $("edit-id").textContent = `${task.id} · REVISION ${task.revision}`;
  $("edit-heading").textContent = task.content.title;
  clear($("task-detail"));
  const dl = el("dl", undefined, "task-detail");
  for (const [label, value] of [
    ["State", labels[task.content.state]], ["Priority", task.content.priority],
    ["Owner", task.content.owner], ["Context & acceptance criteria", task.content.description],
    ["Next action / handoff", task.content.next], ["Blocker", task.content.blocker],
    ["Evidence", task.content.evidence.join("\n")], ["Prerequisites", task.content.depends_on.join(", ")],
  ]) {
    dl.append(el("dt", label));
    const dd = el("dd", value || "None recorded");
    if (label === "Evidence") dd.className = "task-evidence";
    dl.append(dd);
  }
  $("task-detail").append(dl);
  $("history").hidden = !task.history.length;
  clear($("history-items"));
  for (const h of [...task.history].reverse()) {
    const row = el("div", undefined, "history-row");
    row.append(el("strong", `${h.author} · ${new Date(h.at * 1000).toLocaleString()}`), el("pre", JSON.stringify(h.previous, null, 2)));
    $("history-items").append(row);
  }
  if (!$("task-dialog").open) $("task-dialog").showModal();
}
async function refreshRecords() {
  try {
    const data = await api("/api/records");
    const stamp = JSON.stringify(data);
    if (stamp === state.recordStamp && !state.recordsError) return;
    state.records = data.records;
    state.recordsError = "";
    const opened = new Set([...$("records").querySelectorAll("details[open]")].map(d => d.dataset.key));
    state.recordStamp = stamp;
    clear($("records"));
    for (const {kind, record} of data.records) {
      const details = el("details", undefined, "record");
      details.dataset.key = `${kind}/${record.id}`;
      details.open = opened.has(details.dataset.key);
      details.append(el("summary", `${kind} · ${record.id} · ${record.content.title}`),
        el("p", `Revision ${record.revision} · ${record.author || record.content.owner || "Unassigned"}`, "muted"),
        el("pre", record.content.description, "record-body"), el("pre", record.content.evidence.join("\n"), "record-body"));
      $("records").append(details);
    }
    if (!data.records.length)
      message($("records"), "No records yet.", "Ask an agent to write a finding, note or report with e5r project record.");
    renderFunctionNotes();
  } catch (e) {
    state.recordsError = e.message;
    message($("records"), "Records unavailable", e.message);
    renderFunctionNotes();
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
  if (push && state.selected && state.selected.addr !== f.addr) {
    state.history.push(state.selected.addr);
    state.future = [];
  }
  // A call followed from a filtered list must still have a visible selection.
  const query = $("function-search").value.toLowerCase();
  if (!`${f.name} ${f.addr}`.toLowerCase().includes(query))
    $("function-search").value = "";
  const index = state.functions.filter(item =>
    `${item.name} ${item.addr}`.toLowerCase().includes($("function-search").value.toLowerCase()),
  ).findIndex(item => item.addr === f.addr);
  state.functionLimit = Math.max(state.functionLimit, index + 1);
  $("workspace").classList.remove("mobile-functions");
  syncLayout();
  state.selected = f;
  state.context = null;
  state.contextError = "";
  state.instructionTarget = null;
  state.contextPromise = loadContext(f);
  state.code = "";
  $("back").disabled = !state.history.length;
  $("forward").disabled = !state.future.length;
  $("function-name").textContent = f.name;
  $("function-address").textContent = f.addr;
  $("copy-code").disabled = true;
  history.replaceState(null, "", `#workspace/${f.addr}`);
  view("workspace");
  renderFunctions();
  $("functions").querySelector(".selected")?.scrollIntoView({ block: "nearest" });
  renderContext();
  renderAnnotations();
  renderFunctionNotes();
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
    ["Shape", `${f.blocks} blocks · ${f.insns} instructions · ${f.size} bytes`],
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
      "No task linked yet. Ask an agent to link this function as evidence.";
}
function functionNotes() {
  const addr = state.selected?.addr;
  return (state.records || []).filter(({kind, record}) => ["note", "finding", "report"].includes(kind) &&
    record.content.evidence.some(e => e === `function:${addr}` || e === addr));
}
function noteMetadata(record) {
  return `${record.id} · ${record.author || record.content.owner || "Unassigned"} · revision ${record.revision}`;
}
function openNotes() {
  state.pane = "notes";
  if (mobileLayout.matches || !wideLayout.matches) {
    $("workspace").classList.remove("context-open");
    syncLayout();
  }
  loadPane();
  syncTabs();
}
function renderFunctionNotes() {
  if (!state.selected) return;
  const notes = functionNotes();
  clear($("function-notes"));
  $("function-note-count").textContent = state.recordsError ? "Unavailable" : state.records === null ? "Loading…" : String(notes.length);
  if (state.recordsError) $("function-notes").textContent = `Records unavailable: ${state.recordsError}`;
  else if (state.records === null) $("function-notes").textContent = "Loading records…";
  else if (!notes.length) $("function-notes").textContent = `No records linked to ${state.selected.addr}. Link a note with function:${state.selected.addr} as evidence.`;
  else {
    for (const {kind, record} of notes) {
      const button = el("button", undefined, "function-note-preview");
      button.append(el("strong", `${kind} · ${record.content.title}`),
        el("span", record.content.description || "No record text recorded.", "note-excerpt"),
        el("small", noteMetadata(record), "muted"));
      button.onclick = openNotes;
      $("function-notes").append(button);
    }
  }
  if (state.pane === "notes") renderNotesPane();
}
function renderNotesPane() {
  const notes = functionNotes();
  $("quality").className = "quality";
  $("quality").textContent = `Function records · ${state.selected.addr} · Live project records, written by people or agents.`;
  $("analysis-command").textContent = `e5r project record ${shellQuote(state.project.project)} note add 'Note title' --description 'Note text' --evidence function:${state.selected.addr}`;
  $("copy-analysis").disabled = false;
  clear($("code"));
  state.code = "";
  $("copy-code").disabled = true;
  if (state.recordsError) message($("code"), "Records unavailable", state.recordsError);
  else if (state.records === null) message($("code"), "Loading records…");
  else if (!notes.length) message($("code"), "No records for this function yet.", `Ask an agent to save a note with function:${state.selected.addr} as evidence. The command is available in Evidence & tasks.`);
  else {
    for (const {kind, record} of notes) {
      const article = el("article", undefined, "function-note");
      article.append(el("h3", `${kind} · ${record.content.title}`),
        el("p", noteMetadata(record), "muted"),
        el("pre", record.content.description || "No record text recorded.", "record-body"),
        el("p", "Evidence", "muted"), el("pre", record.content.evidence.join("\n") || "None recorded", "record-body"));
      $("code").append(article);
    }
    state.code = notes.map(({kind, record}) => `${kind} · ${record.content.title}\n${record.content.description}`).join("\n\n");
    $("copy-code").disabled = false;
  }
}
function renderBinaryInfo() {
  clear($("binary-info"));
  const info = state.project.info;
  if (!info) {
    message($("binary-info"), "Binary information unavailable", state.project.binary_error);
    return;
  }
  const dl = el("dl");
  for (const [name, value] of [
    ["Format / architecture", `${info.format} · ${info.arch} · ${info.bits}-bit · ${info.endian} endian`],
    ["Entry point", info.entry || "None reported"], ["Image base", info.image_base],
    ["Position independent", info.pic ? "Yes" : "No"],
    ["Contents", `${info.segments} segments · ${info.symbols} symbols · ${info.imports} imports · ${info.exports} exports`],
    ["Function hints", info.function_hints], ["Project content hash", state.project.hash],
    ...Object.entries(info.metadata || {}),
  ]) dl.append(el("dt", name), el("dd", String(value)));
  $("binary-info").append(dl);
  clear($("loader-warnings"));
  $("loader-warnings").hidden = !info.warnings?.length;
  if (info.warnings?.length) $("loader-warnings").append(el("h3", "Loader warnings"));
  for (const warning of info.warnings || []) $("loader-warnings").append(el("p", warning));
}
async function loadContext(f) {
  const serial = ++state.contextRequest;
  try {
    const data = await api(`/api/context/${f.addr}`);
    if (serial !== state.contextRequest) return;
    state.context = data;
    renderAnnotations();
  } catch (e) {
    if (serial !== state.contextRequest) return;
    state.contextError = e.message;
    renderAnnotations();
  }
}
function showPane(pane) {
  if (!wideLayout.matches) {
    $("workspace").classList.remove("context-open", "mobile-functions");
    syncLayout();
  }
  state.pane = pane;
  loadPane();
}
function annotationRow(annotation) {
  const article = el("article", undefined, "annotation-row");
  article.append(el("strong", `${annotation.field} · ${annotation.addr}`),
    el("p", annotation.value, "annotation-text"),
    el("small", `${annotation.author} · asserted · ${annotation.resolution} match${annotation.confident ? "" : " · low confidence"}`, "muted"));
  if (!annotation.confident) article.classList.add("warning");
  return article;
}
function renderAnnotations() {
  clear($("function-annotations"));
  if (state.contextError) $("function-annotations").textContent = `Annotations unavailable: ${state.contextError}`;
  else if (!state.context) $("function-annotations").textContent = "Loading annotations…";
  else if (!state.context.annotations.length) $("function-annotations").textContent = "No saved annotations for this function.";
  else {
    const button = el("button", `Read ${state.context.annotations.length} ${state.context.annotations.length === 1 ? "annotation" : "annotations"}`, "button subtle");
    button.onclick = () => showPane("annotations");
    $("function-annotations").append(button);
    for (const annotation of state.context.annotations.filter(a => a.field === "comment"))
      $("function-annotations").append(annotationRow(annotation));
  }
}
function renderAnnotationPane() {
  clear($("code"));
  for (const annotation of state.context.annotations) $("code").append(annotationRow(annotation));
  if (!state.context.annotations.length) message($("code"), "No saved annotations for this function.");
  $("quality").textContent = "Saved names, types and comments · author and anchor match shown · analysis snapshot";
  state.code = state.context.annotations.map(a => `${a.addr} ${a.field}: ${a.value}\n${a.author} · ${a.resolution}`).join("\n\n");
  $("copy-code").disabled = !state.code;
}
function goInstruction(addr) {
  state.instructionTarget = addr;
  showPane("disas");
}
function addressLink(addr, functionAddr = null) {
  const functionTarget = state.functions.find(f => f.addr === (functionAddr || addr));
  const local = state.context?.blocks.some(b => BigInt(addr) >= BigInt(b.addr) && BigInt(addr) < BigInt(b.end));
  if (!local && !functionTarget) return el("code", addr);
  const button = el("button", addr, "address-link");
  button.onclick = () => local ? goInstruction(addr) : selectFunction(functionTarget);
  return button;
}
function renderDisassembly(data) {
  clear($("code"));
  const known = new Map(state.functions.flatMap(f => [[f.name, f], [f.addr, f]]));
  const lines = [];
  for (const group of data.items || []) for (const insn of group.insns || []) {
    const row = el("div", undefined, "instruction");
    row.dataset.addr = insn.addr;
    const content = el("div", undefined, "instruction-content");
    content.append(syntaxLine(insn.text, known));
    const detail = el("div", undefined, "instruction-detail");
    detail.append(el("span", `${insn.flow} · ${insn.len} bytes`));
    if (insn.target) {
      detail.append(document.createTextNode(" → "), addressLink(insn.target));
      if (insn.target_name) detail.append(document.createTextNode(` <${insn.target_name}>`));
    }
    content.append(detail);
    for (const reference of state.context?.references.filter(r => r.from === insn.addr && ["data", "read", "write"].includes(r.kind)) || [])
      content.append(el("div", `${reference.kind} → ${reference.to} · ${reference.string ? JSON.stringify(reference.string.text) : reference.name || reference.section || "mapped data"}`, "instruction-detail"));
    for (const annotation of state.context?.annotations.filter(a => a.addr === insn.addr && a.field === "comment") || [])
      content.append(el("div", `; ${annotation.value} — ${annotation.author} · ${annotation.resolution} match`, "instruction-comment"));
    row.append(el("code", insn.addr, "instruction-address"), el("code", insn.bytes ?? "Unavailable", "instruction-bytes"), content);
    $("code").append(row);
    const comments = state.context?.annotations.filter(a => a.addr === insn.addr && a.field === "comment") || [];
    lines.push(`${insn.addr}  ${insn.bytes || ""}  ${insn.text}  [${insn.flow}${insn.target ? " → " + insn.target : ""}]${comments.map(a => `\n; ${a.value} — ${a.author} · ${a.resolution} match`).join("")}`);
  }
  if (state.contextError) $("code").prepend(el("p", `Annotations and reference context unavailable: ${state.contextError}`, "context-warning"));
  if (!lines.length) message($("code"), "No decoded instructions for this function.");
  state.code = lines.join("\n");
  $("copy-code").disabled = !state.code;
  if (state.instructionTarget) {
    const selected = [...$("code").querySelectorAll(".instruction")].find(row => row.dataset.addr === state.instructionTarget);
    selected?.classList.add("selected");
    selected?.scrollIntoView({block:"center"});
  } else $("code").scrollTop = 0;
}
function renderOutgoing() {
  clear($("code"));
  const rows = state.context.references.filter(r => state.referenceDirection !== "data" || ["data", "read", "write"].includes(r.kind));
  const table = el("table", undefined, "references outgoing-references");
  const head = el("tr");
  for (const label of ["Instruction", "Kind", "Target", "Target context"]) head.append(el("th", label));
  const thead = el("thead"); thead.append(head); table.append(thead);
  const body = el("tbody");
  for (const r of rows) {
    const row = el("tr"), from = el("td"), target = el("td"), context = el("td");
    from.append(addressLink(r.from)); target.append(addressLink(r.to, r.function));
    if (r.name) context.append(el("strong", r.name));
    if (r.section) context.append(el("div", r.section, "muted"));
    if (r.string) context.append(el("pre", r.string.text, "record-body"), el("small", `${r.string.encoding} string at ${r.string.addr} +${r.string.offset} bytes`, "muted"));
    else context.append(el("code", r.bytes || "No mapped bytes", "data-bytes"));
    row.append(from, el("td", r.kind), target, context); body.append(row);
  }
  table.append(body); $("code").append(table);
  if (!rows.length) message($("code"), "No outgoing references reported in this view.", "References come from every recovered block; unresolved targets are not guessed.");
  $("quality").textContent = `${rows.length} outgoing references · all recovered blocks · ${state.referenceDirection === "data" ? "strings and data" : "code and data"} · analysis snapshot`;
  state.code = JSON.stringify(rows, null, 2); $("copy-code").disabled = !rows.length;
}
$("reference-direction").onchange = () => {
  state.referenceDirection = $("reference-direction").value;
  loadPane();
};
function renderCfg() {
  clear($("code"));
  const blocks = state.context.blocks;
  $("quality").textContent = `${blocks.length} recovered basic blocks · ${state.context.complete ? "Complete" : "Incomplete: " + state.context.halt} · arrows are recovered successors`;
  if (!blocks.length) { message($("code"), "No recovered basic blocks."); return; }
  const byAddr = new Map(blocks.map(b => [b.addr, b]));
  if (blocks.length <= 160) {
    const levels = new Map(), queue = [];
    if (byAddr.has(state.selected.addr)) { levels.set(state.selected.addr, 0); queue.push(state.selected.addr); }
    for (let i = 0; i < queue.length; i++) for (const next of byAddr.get(queue[i])?.successors || []) {
      if (byAddr.has(next) && !levels.has(next)) { levels.set(next, levels.get(queue[i]) + 1); queue.push(next); }
    }
    for (const b of blocks) if (!levels.has(b.addr)) levels.set(b.addr, Math.max(-1, ...levels.values()) + 1);
    const layers = [];
    for (const b of blocks) (layers[levels.get(b.addr)] ||= []).push(b);
    const width = Math.max(1, ...layers.map(row => row?.length || 0)) * 330 + 80;
    const height = layers.length * 190 + 50;
    const canvas = el("div", undefined, "cfg-canvas");
    canvas.style.width = `${width}px`; canvas.style.height = `${height}px`;
    const ns = "http://www.w3.org/2000/svg";
    const svg = document.createElementNS(ns, "svg");
    svg.setAttribute("width", String(width)); svg.setAttribute("height", String(height));
    svg.setAttribute("aria-label", "Recovered control flow edges"); svg.setAttribute("role", "img");
    const defs = document.createElementNS(ns, "defs"), marker = document.createElementNS(ns, "marker");
    for (const [key,value] of Object.entries({id:"cfg-arrow", viewBox:"0 0 10 10", refX:"9", refY:"5", markerWidth:"7", markerHeight:"7", orient:"auto-start-reverse"})) marker.setAttribute(key,value);
    const tip = document.createElementNS(ns,"path"); tip.setAttribute("d","M 0 0 L 10 5 L 0 10 z"); tip.setAttribute("fill","#8cbcff"); marker.append(tip); defs.append(marker); svg.append(defs); canvas.append(svg);
    const positions = new Map();
    layers.forEach((row, level) => row.forEach((block, column) => {
      const left = 40 + (width - 80 - row.length * 330) / 2 + column * 330, top = 20 + level * 190;
      positions.set(block.addr, {x:left + 145, y:top});
      const node = el("article", undefined, `cfg-node${block.unresolved ? " unresolved" : ""}`);
      node.dataset.addr = block.addr; node.style.left = `${left}px`; node.style.top = `${top}px`;
      node.append(el("strong", `${block.addr}${block.addr === state.selected.addr ? " · entry" : ""}`),
        el("p", `${block.insns} instructions · ${block.terminator}${block.unresolved ? " · unresolved" : ""}`));
      const button = el("button", "View instructions", "button subtle"); button.onclick = () => goInstruction(block.addr); node.append(button); canvas.append(node);
    }));
    for (const block of blocks) for (const successor of block.successors) {
      const from = positions.get(block.addr), to = positions.get(successor);
      if (!to) continue; // External successors remain explicit in the table below.
      const path = document.createElementNS(ns, "path"), y = from.y + 130;
      const bend = Math.max(from.x, to.x) + 165;
      path.setAttribute("d", to.y > from.y
        ? `M ${from.x} ${y} C ${from.x} ${y+28}, ${to.x} ${to.y-28}, ${to.x} ${to.y}`
        : `M ${from.x+145} ${from.y+65} C ${bend} ${from.y+65}, ${bend} ${to.y-25}, ${to.x} ${to.y}`);
      path.setAttribute("marker-end", "url(#cfg-arrow)");
      const title = document.createElementNS(ns,"title"); title.textContent = `${block.addr} → ${successor}`; path.append(title); svg.append(path);
    }
    $("code").append(canvas);
  } else $("code").append(el("p", "Large control flow graph: all recovered blocks and successors are listed below.", "context-warning"));
  const table = el("table", undefined, "references cfg-table"), head = el("tr"), thead = el("thead");
  for (const label of ["Block", "End (exclusive)", "Ending", "Successors"]) head.append(el("th", label));
  thead.append(head); table.append(thead); const body = el("tbody");
  table.append(body); $("code").append(table);
  let shown = 0;
  const more = el("button", "", "button subtle cfg-more");
  const appendBlocks = () => {
    const batch = blocks.slice(shown, shown + 200);
    for (const block of batch) {
      const row = el("tr"), address = el("td"), successors = el("td"); address.append(addressLink(block.addr));
      for (const addr of block.successors) successors.append(addressLink(addr), document.createTextNode(byAddr.has(addr) ? " " : " (outside recovered blocks) "));
      if (!block.successors.length) successors.textContent = block.unresolved ? "Unresolved" : "None";
      row.append(address, el("td", block.end), el("td", `${block.terminator}${block.unresolved ? " · unresolved" : ""}`), successors); body.append(row);
    }
    shown += batch.length;
    more.hidden = shown >= blocks.length;
    more.textContent = `Show next ${Math.min(200, blocks.length - shown)} blocks (${shown} / ${blocks.length} shown)`;
  };
  more.onclick = appendBlocks;
  appendBlocks(); $("code").append(more);
  state.code = JSON.stringify(blocks, null, 2); $("copy-code").disabled = false;
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
    if (target && !["comment", "string"].includes(style)) {
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
  $("code").scrollTop = 0;
  $("code").scrollLeft = 0;
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
  state.code = "";
  $("copy-code").disabled = true;
  const rows = data.items || [];
  if (!rows.length) {
    message(
      $("code"),
      "No incoming references reported.",
      "This is the analysis result for this analysis snapshot.",
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
function renderCallGraph(data) {
  clear($("code"));
  const graph = el("div", undefined, "call-graph");
  const addr = state.selected.addr;
  const callers = [...new Set(data.edges.filter(edge => edge.to === addr).map(edge => edge.from))];
  const callees = [...new Set(data.edges.filter(edge => edge.from === addr).map(edge => edge.to))];
  for (const [label, addresses] of [["Callers →", callers], ["Selected function", [addr]], ["→ Callees", callees]]) {
    const column = el("section", undefined, "call-column");
    column.append(el("h3", `${label} (${addresses.length})`));
    for (const target of addresses) {
      const f = state.functions.find(f => f.addr === target);
      const current = label === "Selected function";
      const node = el(f && !current ? "button" : "div", f ? `${f.name}\n${target}` : target, `call-node${current ? " current" : ""}`);
      if (f && !current) node.onclick = () => selectFunction(f);
      column.append(node);
    }
    if (!addresses.length) column.append(el("p", "None recovered", "muted"));
    graph.append(column);
  }
  $("code").append(graph);
  state.code = JSON.stringify(data, null, 2);
  $("copy-code").disabled = false;
}

async function loadPane() {
  if (!state.selected) return;
  $("variables-section").hidden = true;
  const serial = ++state.request,
    f = state.selected,
    pane = state.pane;
  document
    .querySelectorAll("[data-pane]")
    .forEach((b) =>
      b.setAttribute("aria-selected", String(b.dataset.pane === pane)),
    );
  $("reference-controls").hidden = pane !== "xrefs";
  syncTabs();
  if (pane === "notes") {
    renderNotesPane();
    return;
  }
  $("quality").className = "quality";
  if (["cfg", "annotations"].includes(pane) || (pane === "xrefs" && state.referenceDirection !== "incoming")) {
    message($("code"), "Loading function context…");
    $("quality").textContent = "Loading function context…";
    state.code = "";
    $("copy-code").disabled = true;
    $("copy-analysis").disabled = true;
    await state.contextPromise;
    if (serial !== state.request) return;
    if (state.contextError) { message($("code"), "Function context unavailable", state.contextError); $("quality").textContent = "Context unavailable"; return; }
    if (pane === "cfg") renderCfg();
    else if (pane === "annotations") renderAnnotationPane();
    else renderOutgoing();
    $("analysis-command").textContent = pane === "annotations"
      ? `e5r annotate ${shellQuote(state.project.binary)} list${state.project.log ? " --db " + shellQuote(state.project.log) : ""}`
      : `Function ${pane === "cfg" ? "control flow" : "outgoing references"} from the analysis snapshot.`;
    $("copy-analysis").disabled = pane !== "annotations";
    return;
  }
  $("quality").className = "quality";
  $("quality").textContent =
    `Loading ${pane === "decompile" ? "pseudocode" : pane === "disas" ? "disassembly" : pane === "callgraph" ? "call graph" : "references"}…`;
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
  $("copy-analysis").disabled = pane === "callgraph";
  if (pane === "callgraph") $("analysis-command").textContent = "Call graph from recovered CFG direct-call edges.";
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
      await state.contextPromise;
      if (serial !== state.request) return;
      renderDisassembly(data);
      $("quality").textContent =
        `${f.insns} instructions · ${f.strength} boundary · ${f.complete ? "Complete" : "Incomplete: " + f.halt}`;
    } else if (pane === "callgraph") {
      renderCallGraph(data);
      $("quality").textContent = "Incoming → outgoing direct calls around this function. Click a node to navigate. Indirect targets are not resolved.";
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
$("refresh").onclick = () => { refreshTasks(); refreshRecords(); };
$("close-dialog").onclick = () => $("task-dialog").close();
$("expand-task").onclick = () => {
  const expanded = $("task-dialog").classList.toggle("full-view");
  $("expand-task").textContent = expanded ? "← Back to popup" : "Full view";
};
$("task-dialog").addEventListener("close", () => {
  $("task-dialog").classList.remove("full-view");
  $("expand-task").textContent = "Full view";
});
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
function navigateHistory(forward = false) {
  const source = forward ? state.future : state.history;
  const destination = forward ? state.history : state.future;
  const addr = source.pop();
  const f = state.functions.find(f => f.addr === addr);
  if (!f) return;
  if (state.selected) destination.push(state.selected.addr);
  selectFunction(f, false);
}
$("back").onclick = () => navigateHistory();
$("forward").onclick = () => navigateHistory(true);

const mobileLayout = matchMedia("(max-width: 700px)");
const wideLayout = matchMedia("(min-width: 1101px)");
function syncLayout() {
  const workspace = $("workspace");
  $("toggle-functions").setAttribute("aria-expanded", String(mobileLayout.matches
    ? workspace.classList.contains("mobile-functions")
    : !workspace.classList.contains("functions-hidden")));
  $("toggle-context").setAttribute("aria-expanded", String(workspace.classList.contains("context-open")));
}
$("workspace").classList.toggle("context-open", wideLayout.matches);
$("toggle-functions").onclick = () => {
  $("workspace").classList.toggle(mobileLayout.matches ? "mobile-functions" : "functions-hidden");
  if (mobileLayout.matches) $("workspace").classList.remove("context-open");
  syncLayout();
};
$("toggle-context").onclick = () => {
  $("workspace").classList.toggle("context-open");
  $("workspace").classList.remove("mobile-functions");
  syncLayout();
};
mobileLayout.addEventListener("change", () => {
  $("workspace").classList.remove("mobile-functions", "functions-hidden");
  syncLayout();
});
syncLayout();
let codeSize = Number(localStorage.getItem("e5r.code-size") || 14);
if (!Number.isFinite(codeSize)) codeSize = 14;
function resizeCode(delta = 0) {
  codeSize = Math.max(12, Math.min(22, codeSize + delta));
  document.documentElement.style.setProperty("--code-size", `${codeSize}px`);
  $("font-size").textContent = `${codeSize}px`;
  $("font-smaller").disabled = codeSize <= 12;
  $("font-larger").disabled = codeSize >= 22;
  localStorage.setItem("e5r.code-size", String(codeSize));
}
$("font-smaller").onclick = () => resizeCode(-1);
$("font-larger").onclick = () => resizeCode(1);
resizeCode();
window.addEventListener("hashchange", route);
window.addEventListener("keydown", (e) => {
  if ($("workspace").hidden || $("task-dialog").open ||
    ["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName)) return;
  if (e.key === "/") {
    e.preventDefault();
    $("workspace").classList.remove("functions-hidden");
    if (mobileLayout.matches) {
      $("workspace").classList.add("mobile-functions");
      $("workspace").classList.remove("context-open");
    }
    syncLayout();
    $("function-search").focus();
  } else if (e.altKey && ["ArrowLeft", "ArrowRight"].includes(e.key)) {
    e.preventDefault();
    navigateHistory(e.key === "ArrowRight");
  } else if (e.key === "Escape") {
    $("workspace").classList.remove("mobile-functions");
    if (!wideLayout.matches) $("workspace").classList.remove("context-open");
    syncLayout();
  }
});
const tabs = [...document.querySelectorAll("[data-pane]")];
function syncTabs() {
  tabs.forEach(tab => {
    tab.tabIndex = tab.dataset.pane === state.pane ? 0 : -1;
    tab.setAttribute("aria-selected", String(tab.dataset.pane === state.pane));
  });
}
for (const tab of tabs) {
  tab.addEventListener("click", syncTabs);
  tab.addEventListener("keydown", e => {
    if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(e.key)) return;
    e.preventDefault();
    const index = e.key === "Home" ? 0 : e.key === "End" ? tabs.length - 1
      : (tabs.indexOf(tab) + (e.key === "ArrowRight" ? 1 : -1) + tabs.length) % tabs.length;
    tabs[index].click();
    tabs[index].focus();
  });
}
syncTabs();

async function boot() {
  try {
    state.project = await api("/api/project");
    const name = state.project.name || state.project.project.split("/").pop();
    $("all-projects").hidden = !state.project.collection;
    $("project-name").textContent = name;
    document.title = `${name} · e5r`;
    $("binary-name").textContent = state.project.binary;
    renderBinaryInfo();
    $("agent-command").textContent =
      `e5r project task ${shellQuote(state.project.project)} list --json`;
    renderBoard();
    await refreshTasks();
    await refreshRecords();
    if (state.project.binary_error)
      error(
        `Binary unavailable: ${state.project.binary_error}. Project tasks remain available.`,
      );
    route();
    setInterval(() => { refreshTasks(); refreshRecords(); }, 5000);
  } catch (e) {
    error(`Could not open project: ${e.message}`);
    $("sync").textContent = "Unavailable";
  }
}
boot();
