// Optional global-project integration check; same Playwright setup as test-dashboard.mjs.
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import {
  mkdtempSync,
  writeFileSync,
  readFileSync,
  renameSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
const { chromium } = await import(
  process.env.E5R_PLAYWRIGHT_MODULE || "playwright"
);
const root = mkdtempSync(join(tmpdir(), "e5r-projects-"));
const executable = resolve(process.env.E5R_BINARY || "target/release/e5r");
const env = { ...process.env, E5R_PROJECT_HOME: join(root, "registry") };
const binary = join(root, "sample"),
  local = join(root, "local.e5rproj");
const cli = (...args) =>
  execFileSync(executable, args, { env, cwd: tmpdir(), encoding: "utf8" });
let server, browser;
try {
  writeFileSync(join(root, "sample.c"), "int main(void) { return 3; }\n");
  execFileSync("cc", ["-g", "-O0", join(root, "sample.c"), "-o", binary]);
  cli("project", "new", binary, "--name", "alpha");
  cli("project", "new", binary, "--out", local);
  const task = JSON.parse(
    cli(
      "project",
      "task",
      local,
      "add",
      "Inspect entry point",
      "--owner",
      "agent-a",
      "--next",
      "Read main",
    ),
  );
  for (const kind of ["finding", "note", "report"]) {
    cli("project", "record", local, kind, "add", `${kind} title`, "--description", "Body retained on import");
  }
  cli("project", "import", local, "--name", "beta");
  for (const kind of ["finding", "note", "report"]) {
    assert.deepEqual(JSON.parse(cli("project", "record", "beta", kind, "list", "--json")), JSON.parse(cli("project", "record", local, kind, "list", "--json")));
  }
  assert.deepEqual(
    JSON.parse(cli("project", "task", "beta", "list", "--json")),
    JSON.parse(cli("project", "task", local, "list", "--json")),
  );
  assert.equal(JSON.parse(cli("project", "list", "--json")).projects.length, 2);
  assert.match(
    readFileSync(
      join(env.E5R_PROJECT_HOME, "alpha", "project.e5rproj"),
      "utf8",
    ),
    new RegExp(binary),
  );
  const url = await new Promise((ok, fail) => {
    server = spawn(executable, ["ui", "--port", "0"], {
      env,
      cwd: tmpdir(),
      stdio: ["ignore", "pipe", "pipe"],
    });
    let log = "";
    const timer = setTimeout(() => fail(new Error(log)), 30000);
    server.stderr.on("data", (d) => {
      log += d;
      const m = log.match(/Project collection: (http:\/\/127\.0\.0\.1:\d+)/);
      if (m) {
        clearTimeout(timer);
        ok(m[1]);
      }
    });
    server.on("exit", (c) => {
      clearTimeout(timer);
      fail(new Error(`server exited ${c}: ${log}`));
    });
  });
  assert.equal((await fetch(url + "/p/")).status, 404);
  assert.equal((await fetch(url + "/api/projects")).status, 200);
  assert.equal(
    (await (await fetch(url + "/p/alpha/api/tasks")).json()).tasks.length,
    0,
  );
  assert.equal(
    (await (await fetch(url + "/p/beta/api/tasks")).json()).tasks[0].task.id,
    task.id,
  );
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({
    viewport: { width: 1440, height: 960 },
  });
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto(url);
  await page.locator("#project-rows .project-link").first().waitFor();
  assert.equal(await page.locator("#project-rows .project-link").count(), 2);
  await page.screenshot({ path: "/tmp/e5r-projects.png", fullPage: true });
  assert.equal(await page.locator("#new-project").count(), 0);
  assert.equal((await fetch(url + "/api/projects", {method:"POST", headers:{"X-E5R-Client":"dashboard","Content-Type":"application/json"}, body:JSON.stringify({name:"gamma", binary})})).status, 405);
  cli("project", "new", binary, "--name", "gamma");
  await page.locator("#refresh").click();
  await page.waitForFunction(() => document.querySelectorAll("#project-rows .project-link").length === 3);
  await page.goto(url + `/p/beta/#task/${task.id}`);
  await page.locator("dialog[open]").waitFor();
  assert.equal(
    await page.locator("#edit-heading").textContent(),
    "Inspect entry point",
  );
  const functions = await (await fetch(url + "/p/beta/api/functions")).json();
  const main = functions.items.find((f) => f.name === "main");
  assert(main);
  const pane = await (
    await fetch(url + `/p/beta/api/decompile/${main.addr}`)
  ).json();
  assert.deepEqual(
    pane,
    JSON.parse(cli("decompile", binary, main.addr, "--json")),
  );
  cli("project", "new", binary);
  const collision = JSON.parse(
    execFileSync(executable, ["project", "task", "sample", "list", "--json"], {
      env,
      cwd: root,
      encoding: "utf8",
    }),
  );
  assert.equal(
    collision.tasks.length,
    0,
    "registered name must beat a same-named binary",
  );
  const moved = join(root, "moved");
  renameSync(binary, moved);
  assert.equal(
    (await (await fetch(url + "/api/projects")).json()).projects.find(
      (p) => p.name === "alpha",
    ).availability,
    "missing",
  );
  assert(
    (await (await fetch(url + "/p/alpha/api/project")).json()).binary_error,
  );
  assert.equal((await fetch(url + "/p/alpha/api/tasks")).status, 200);
  cli("project", "relocate", "alpha", moved);
  assert.equal(
    (await (await fetch(url + "/api/projects")).json()).projects.find(
      (p) => p.name === "alpha",
    ).availability,
    "available",
  );
  assert.equal(errors.length, 0, errors.join("\n"));
  console.log(
    "Global projects: registration, import, cwd independence, isolated tasks, read-only collection and CLI creation, decompiler and relocation passed.",
  );
} finally {
  if (browser) await browser.close();
  if (server && server.exitCode === null) {
    server.kill();
    await new Promise((ok) => server.once("exit", ok));
  }
  rmSync(root, { recursive: true, force: true });
}
