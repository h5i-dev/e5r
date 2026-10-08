// Optional browser integration check. Requires Playwright + Chromium, and cc.
// E5R_PLAYWRIGHT_MODULE may point to an out-of-tree Playwright installation.
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import { mkdtempSync, writeFileSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { get } from "node:http";
const { chromium } = await import(
  process.env.E5R_PLAYWRIGHT_MODULE || "playwright"
);
const root = mkdtempSync(join(tmpdir(), "e5r-dashboard-"));
const executable = resolve(process.env.E5R_BINARY || "target/release/e5r");
const binary = join(root, "sample"),
  project = join(root, "sample.e5rproj");
let server, browser;
function cli(...args) {
  return execFileSync(executable, args, { encoding: "utf8" });
}
try {
  writeFileSync(
    join(root, "sample.c"),
    `__attribute__((noinline)) int parse_header(int length) { if(length < 0 || length > 32) return -1; return length + 1; }\nint main(void) { return parse_header(4) == 5 ? 0 : 1; }\n`,
  );
  execFileSync("cc", ["-g", "-O0", join(root, "sample.c"), "-o", binary]);
  cli("project", "new", binary, "--out", project);
  const task = JSON.parse(
    cli(
      "project",
      "task",
      project,
      "add",
      "Trace input validation",
      "--owner",
      "agent-a",
      "--next",
      "Inspect parser guard",
      "--priority",
      "high",
    ),
  );
  const url = await new Promise((ok, fail) => {
    server = spawn(
      executable,
      ["project", "dashboard", project, "--port", "0"],
      { stdio: ["ignore", "pipe", "pipe"] },
    );
    let log = "";
    const timer = setTimeout(
      () => fail(new Error("server startup timed out: " + log)),
      30000,
    );
    server.stderr.on("data", (d) => {
      log += d;
      const m = log.match(/Project workspace: (http:\/\/127\.0\.0\.1:\d+)/);
      if (m) {
        clearTimeout(timer);
        ok(m[1]);
      }
    });
    server.on("exit", (code) => {
      clearTimeout(timer);
      fail(new Error(`server exited ${code}: ${log}`));
    });
  });
  const functions = await (await fetch(url + "/api/functions")).json();
  const main = functions.items.find((f) => f.name === "main");
  assert(main);
  const decompiled = await (
    await fetch(url + `/api/decompile/${main.addr}`)
  ).json();
  const cliDecompiled = JSON.parse(
    cli("decompile", binary, main.addr, "--json"),
  );
  assert.deepEqual(decompiled, cliDecompiled, "pane output must equal the CLI");
  assert.equal(
    (
      await fetch(url + "/api/tasks", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: "{}",
      })
    ).status,
    405,
  );
  assert.equal(
    (
      await fetch(url + "/api/tasks", {
        headers: { Origin: "https://attacker.example" },
      })
    ).status,
    403,
  );
  assert.equal(
    await new Promise((ok, fail) => {
      get(
        url + "/api/tasks",
        { headers: { Host: "attacker.example" } },
        (response) => {
          response.resume();
          ok(response.statusCode);
        },
      ).on("error", fail);
    }),
    403,
  );
  assert.equal((await fetch(url + "/api/decompile/all")).status, 400);
  assert.equal(
    (
      await fetch(url + "/api/tasks", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "X-E5R-Client": "dashboard",
        },
        body: "x".repeat(128 * 1024 + 1),
      })
    ).status,
    405,
  );
  browser = await chromium.launch({ headless: true, args: ["--no-sandbox"] });
  const page = await browser.newPage({
    viewport: { width: 1440, height: 1050 },
  });
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto(url);
  await page
    .locator("#headline")
    .filter({ hasText: "The next step is clear." })
    .waitFor();
  await page
    .getByRole("button", { name: "Trace input validation", exact: true })
    .click();
  assert.equal(await page.locator("#task-dialog input, #task-dialog textarea, #task-dialog select").count(), 0);
  await page.locator("#expand-task").click();
  assert(await page.locator("#task-dialog").evaluate(e => e.classList.contains("full-view")));
  await page.screenshot({path:"/tmp/e5r-dashboard-task-full.png", fullPage:true});
  await page.locator("#expand-task").click();
  assert(!(await page.locator("#task-dialog").evaluate(e => e.classList.contains("full-view"))));
  const draft = { ...task.content, next: "Agent update", evidence: ["Evidence line\n".repeat(100)] };
  const input = join(root, "edit.json");
  writeFileSync(input, JSON.stringify(draft));
  cli("project", "task", project, "update", task.id, "--revision", "1", "--input", input, "--author", "agent-b");
  await page.locator("#task-detail").filter({hasText: "Agent update"}).waitFor();
  assert(await page.locator(".task-evidence").evaluate(e => e.getBoundingClientRect().height >= 150));
  await page.locator("#close-dialog").click();
  for (const kind of ["finding", "note", "report"]) {
    cli("project", "record", project, kind, "add", `${kind} title`, "--description", '<img src=x onerror="window.taskXss=true">', "--evidence", `function:${main.addr}`, "--author", "agent-b");
  }
  const record = JSON.parse(cli("project", "record", project, "finding", "list", "--json")).tasks[0].task;
  writeFileSync(input, JSON.stringify({...record.content, description:"Updated finding"}));
  cli("project", "record", project, "finding", "update", record.id, "--revision", "1", "--input", input);
  assert.throws(() => cli("project", "record", project, "finding", "update", record.id, "--revision", "1", "--input", input), /revision conflict/);
  assert.equal(JSON.parse(cli("project", "record", project, "finding", "list", "--json")).tasks[0].task.history.length, 1);
  await page.locator("#refresh").click();
  await page.locator("#records summary").filter({hasText:"report title"}).waitFor();
  assert.equal(await page.locator("#records img").count(), 0);
  await page.locator("#records summary").filter({hasText:"report title"}).click();
  await page.locator("#refresh").click();
  assert(await page.locator("#records details").filter({hasText:"report title"}).evaluate(e => e.open));
  await page.screenshot({
    path: "/tmp/e5r-dashboard-overview.png",
    fullPage: true,
  });
  await page.locator("#nav-workspace").click();
  await page.locator("#function-search").fill("main");
  await page.locator('.function-row[title="main"]').click();
  await page.locator(".line-source").first().waitFor();
  assert.equal(await page.locator("#function-name").textContent(), "main");
  assert(await page.locator("#code").textContent());
  await page.screenshot({
    path: "/tmp/e5r-dashboard-decompiler.png",
    fullPage: true,
  });
  await page
    .locator("#code a.call")
    .filter({ hasText: "parse_header" })
    .first()
    .click();
  await page
    .locator("#function-name")
    .filter({ hasText: "parse_header" })
    .waitFor();
  // Following a call keeps the function browser synchronized, even after filtering.
  assert.equal(await page.locator("#function-search").inputValue(), "");
  assert.equal(await page.locator(".function-row.selected strong").textContent(), "parse_header");
  await page.locator("#back").click();
  await page.locator("#function-name").filter({ hasText: "main" }).waitFor();
  await page.locator("#forward").click();
  await page.locator("#function-name").filter({ hasText: "parse_header" }).waitFor();
  await page.keyboard.press("Alt+ArrowLeft");
  await page.locator("#function-name").filter({ hasText: "main" }).waitFor();
  await page.locator("#font-larger").click();
  assert.equal(await page.locator(".code-line").first().evaluate(e => getComputedStyle(e).fontSize), "15px");
  assert.equal(await page.evaluate(() => localStorage.getItem("e5r.code-size")), "15");
  await page.locator("#toggle-context").click();
  assert.equal(await page.locator("#inspector").isVisible(), false);
  await page.locator("#toggle-functions").click();
  assert.equal(await page.locator("#function-pane").isVisible(), false);
  await page.locator("#toggle-functions").click();
  await page.locator("#toggle-context").click();
  await page.getByRole("tab", { name: "Disassembly" }).click();
  await page.locator("#quality").filter({ hasText: "instructions" }).waitFor();
  assert((await page.locator("#code").textContent()).includes(main.addr));
  await page.getByRole("tab", { name: "Disassembly" }).focus();
  await page.keyboard.press("ArrowRight");
  assert.equal(await page.getByRole("tab", { name: "References" }).getAttribute("aria-selected"), "true");
  await page
    .locator("#quality")
    .filter({ hasText: "Incoming references" })
    .waitFor();
  await page.getByRole("tab", { name: "Call graph" }).click();
  await page.locator(".call-node").filter({hasText:"parse_header"}).first().waitFor();
  await page.screenshot({path:"/tmp/e5r-dashboard-callgraph.png", fullPage:true});
  await page.locator(".call-node").filter({hasText:"parse_header"}).first().click();
  await page.locator("#function-name").filter({hasText:"parse_header"}).waitFor();
  await page.locator(".call-node").filter({hasText:"main"}).first().waitFor();
  assert.equal(await page.evaluate(() => window.taskXss), undefined);
  await page.setViewportSize({ width: 390, height: 844 });
  if (await page.locator("#inspector").isVisible()) await page.locator("#toggle-context").click();
  assert.equal(await page.locator("#function-pane").isVisible(), false);
  await page.locator("#toggle-context").click();
  assert.equal(await page.locator("#inspector").isVisible(), true, "evidence stays reachable on mobile");
  await page.locator("#toggle-context").click();
  await page.keyboard.press("/");
  assert.equal(await page.locator("#function-pane").isVisible(), true);
  await page.locator("#function-search").fill("main");
  await page.locator('.function-row[title="main"]').click();
  assert.equal(await page.locator("#function-pane").isVisible(), false);
  await page.getByRole("tab", { name: "Pseudocode" }).click();
  await page.locator(".line-source").first().waitFor();
  await page.screenshot({
    path: "/tmp/e5r-dashboard-mobile.png",
    fullPage: true,
  });
  assert.equal(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= innerWidth,
    ),
    true,
    "mobile layout must fit",
  );
  assert.deepEqual(errors, [], "no browser runtime errors");
  // Store writes should retain authors and history across a server restart.
  const saved = JSON.parse(
    readFileSync(join(project + ".work", task.id + ".json"), "utf8"),
  );
  assert.equal(saved.revision, 2);
  assert.equal(saved.history.length, 1);
  console.log(
    "Dashboard integration passed: CLI parity, read-only UI, live agent updates, full task view, records, call graph, synchronized function navigation, back/forward history, reading controls, keyboard tabs, mobile evidence, XSS, mobile layout, HTTP boundaries.",
  );
} finally {
  if (browser) await browser.close();
  if (server) {
    server.kill("SIGTERM");
    await new Promise((ok) =>
      server.exitCode !== null ? ok() : server.once("exit", ok),
    );
  }
  rmSync(root, { recursive: true, force: true });
}
