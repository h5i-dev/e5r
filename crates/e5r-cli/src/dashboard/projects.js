"use strict";
const $ = (id) => document.getElementById(id);
let projects = [],
  last = "";
function el(tag, text, className) {
  const e = document.createElement(tag);
  if (text !== undefined) e.textContent = text;
  if (className) e.className = className;
  return e;
}
function link(name, hash = "overview") {
  return `/p/${encodeURIComponent(name)}/#${hash}`;
}
const availability = {
  available: "Available",
  missing: "Missing",
  size_changed: "Size changed",
  unreadable: "Unreadable",
};
function render() {
  const attention = projects.flatMap((p) =>
      p.attention.map((t) => ({ ...t, project: p.name })),
    ),
    errors = projects.filter((p) => p.error || p.availability !== "available");
  $("headline").textContent = attention.length
    ? `${attention.length} ${attention.length === 1 ? "item needs" : "items need"} attention.`
    : errors.length
      ? `${errors.length} ${errors.length === 1 ? "project needs" : "projects need"} a closer look.`
      : projects.length
        ? "Your projects are in view."
        : "Start your first investigation.";
  $("headline-sub").textContent = projects.length
    ? `${projects.length} projects · task updates appear here automatically. Open a project to keep its next step clear.`
    : "Ask an agent to run e5r project new PATH --name NAME. Existing manifests can be imported with e5r project import.";
  $("counts").replaceChildren();
  for (const [n, label, tone] of [
    [projects.length, "projects", ""],
    [projects.reduce((n, p) => n + p.counts.active, 0), "active tasks", ""],
    [attention.length + errors.length, "need attention", "attention"],
  ]) {
    const c = el("div", undefined, `count ${tone}`);
    c.append(el("b", String(n)), el("span", label));
    $("counts").append(c);
  }
  $("attention").replaceChildren();
  $("attention-count").textContent = String(attention.length + errors.length);
  for (const t of attention.slice(0, 10)) {
    const a = el("a", undefined, "work-row collection-row");
    a.href = link(t.project, `task/${t.id}`);
    const title = el("div", undefined, "work-row-title");
    title.append(
      el("span", `${t.project} / ${t.id} · ${t.title}`),
      el(
        "span",
        t.state === "review" ? "Review" : "Blocked",
        `state ${t.state}`,
      ),
    );
    a.append(
      title,
      el("div", t.why + (t.owner ? ` · ${t.owner}` : ""), "work-row-sub"),
    );
    $("attention").append(a);
  }
  for (const p of errors) {
    const a = el("a", undefined, "work-row collection-row");
    a.href = link(p.name);
    a.append(
      el("div", p.name, "work-row-title"),
      el(
        "div",
        p.error ||
          `${availability[p.availability]} binary: ${p.binary}. Tasks remain available; use e5r project relocate ${p.name} PATH for a moved binary.`,
        "work-row-sub",
      ),
    );
    $("attention").append(a);
  }
  if (!attention.length && !errors.length) {
    const e = el("div", undefined, "empty");
    e.append(
      el("strong", "Nothing is waiting on you."),
      el(
        "span",
        "No task is blocked or awaiting review, and every binary path is available.",
      ),
    );
    $("attention").append(e);
  }
  if (attention.length > 10)
    $("attention").append(
      el(
        "div",
        `${attention.length - 10} more attention items inside their projects.`,
        "empty",
      ),
    );
  renderProjects();
}
function renderProjects() {
  const query = $("search").value.toLowerCase(),
    filter = $("filter").value;
  const visible = projects.filter(
    (p) =>
      `${p.name} ${p.binary || ""}`.toLowerCase().includes(query) &&
      (filter === "all" ||
        (filter === "attention" &&
          (p.attention.length || p.error || p.availability !== "available")) ||
        (filter === "active" && p.counts.active) ||
        (filter === "unavailable" && p.availability !== "available")),
  );
  $("project-rows").replaceChildren();
  for (const p of visible) {
    const tr = el("tr"),
      name = el("td"),
      a = el("a", p.name, "project-link");
    a.href = link(p.name);
    name.append(a, el("span", p.binary || "Unreadable manifest", "task-note"));
    if (p.error) name.append(el("span", p.error, "project-error"));
    tr.append(
      name,
      el("td", `${p.counts.open} / ${p.counts.total}`),
      el("td", String(p.counts.active)),
      el("td", `${p.counts.blocked} blocked · ${p.counts.review} review`),
      el(
        "td",
        availability[p.availability] || p.availability,
        p.availability === "available" ? "muted" : "project-error",
      ),
    );
    $("project-rows").append(tr);
  }
  $("empty").hidden = !!visible.length;
  $("empty").textContent = projects.length
    ? "No projects match this view."
    : "No projects registered. Ask an agent to register or import a project through the CLI.";
}
async function refresh() {
  try {
    const response = await fetch("/api/projects"),
      data = await response.json();
    if (!response.ok) throw new Error(data.error);
    const stamp = JSON.stringify(data);
    projects = data.projects;
    $("storage").textContent = data.root;
    if (stamp !== last) {
      last = stamp;
      render();
    }
    $("sync").textContent = "Projects up to date";
    $("error").hidden = true;
  } catch (e) {
    $("error").textContent = `Could not refresh projects: ${e.message}`;
    $("error").hidden = false;
    $("sync").textContent = "Unavailable";
  }
}
$("refresh").onclick = refresh;
$("search").oninput = renderProjects;
$("filter").onchange = renderProjects;
$("copy-command").onclick = async () => {
  try {
    await navigator.clipboard.writeText("e5r project list --json");
    $("copy-command").textContent = "Copied";
    setTimeout(() => ($("copy-command").textContent = "Copy command"), 1200);
  } catch {}
};
refresh();
setInterval(refresh, 5000);
