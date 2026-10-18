// The Set Theory Game: a guided path through Grace17, one checked theorem at a time.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { requestWorkbench } from "./worker-client.js";
import { forbiddenTacticUsed, levelSource, worlds } from "./game-levels.js";
import { highlightGrace17 } from "./tactics-guide.js";
import { unicodeCompletionAt } from "./editor-utils.js";
import { workbenchSourceLink } from "./deep-links.js";

const STORAGE_KEY = "grace17-set-theory-game";
const levels = worlds.flatMap(world => world.levels.map(level => ({ world, level, id: `${world.id}.${level.id}` })));
const byId = new Map(levels.map(entry => [entry.id, entry]));

const $ = id => document.getElementById(id);
const escapeHtml = text => String(text).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);

function loadProgress() {
  try { return { solved: {}, drafts: {}, ...JSON.parse(localStorage.getItem(STORAGE_KEY) || "{}") }; }
  catch { return { solved: {}, drafts: {} }; }
}
function saveProgress() {
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(progress)); } catch { /* storage may be unavailable */ }
}
const progress = loadProgress();

let current = null;
let revealedHints = 0;
let checking = false;
let checkSerial = 0;

function fileName(entry) { return `${entry.world.id}-${entry.level.id}.g17`; }
function bodyOffset(entry) {
  // Lines of the generated module before the first proof line.
  return levelSource(entry.world, entry.level, "").split("\n").length - 1;
}

function renderWorlds() {
  const nav = $("worlds");
  nav.innerHTML = worlds.map(world => `<h2>${escapeHtml(world.title)}<small>${escapeHtml(world.subtitle)}</small></h2><ol>${
    world.levels.map((level, index) => {
      const id = `${world.id}.${level.id}`;
      const classes = [current?.id === id ? "current" : "", progress.solved[id] ? "solved" : ""].filter(Boolean).join(" ");
      return `<li><a href="#${encodeURIComponent(id)}" class="${classes}" data-level="${escapeHtml(id)}"><span class="mark" aria-hidden="true"></span><span class="index">${index + 1}</span><span>${escapeHtml(level.title)}</span></a></li>`;
    }).join("")}</ol>`).join("");
  const solved = levels.filter(entry => progress.solved[entry.id]).length;
  $("progress").textContent = `${solved} / ${levels.length} levels`;
}

function openLevel(id, { pushHash = true } = {}) {
  const entry = byId.get(id) ?? levels[0];
  current = entry;
  revealedHints = 0;
  if (pushHash && decodeURIComponent(location.hash.slice(1)) !== entry.id) history.replaceState(null, "", `#${encodeURIComponent(entry.id)}`);
  $("worldTitle").textContent = entry.world.title;
  $("levelTitle").textContent = entry.level.title;
  const firstOfWorld = entry.world.levels[0] === entry.level;
  $("worldIntro").innerHTML = firstOfWorld ? entry.world.intro : "";
  $("worldIntro").hidden = !firstOfWorld;
  $("levelText").innerHTML = entry.level.text;
  const statementText = (entry.level.preamble ? `${entry.level.preamble.trimEnd()}\n\n` : "") + entry.level.statement.trimEnd();
  $("statement").querySelector("code").innerHTML = highlightGrace17(statementText);
  const forbid = entry.level.forbid ?? [];
  $("rules").hidden = forbid.length === 0;
  $("rules").innerHTML = forbid.length ? `By hand: ${forbid.map(name => `<code>${escapeHtml(name)}</code>`).join(", ")} ${forbid.length === 1 ? "is" : "are"} switched off for this level.` : "";
  const editor = $("editor");
  editor.value = progress.drafts[entry.id] ?? entry.level.starter;
  editor.rows = Math.max(6, editor.value.split("\n").length + 2);
  $("hints").hidden = true;
  $("hints").innerHTML = "";
  $("hint").disabled = false;
  $("previous").disabled = levels.indexOf(entry) === 0;
  $("next").disabled = levels.indexOf(entry) === levels.length - 1;
  $("result").innerHTML = '<p class="muted">Checking the starting goal…</p>';
  $("resultMeta").textContent = "";
  updateWorkbenchLink();
  renderWorlds();
  document.title = `${entry.level.title} · The Set Theory Game`;
  void check({ silent: true });
}

function updateWorkbenchLink() {
  if (!current) return;
  const source = levelSource(current.world, current.level, $("editor").value);
  $("openWorkbench").href = workbenchSourceLink(fileName(current), source, "./", bodyOffset(current) + 1);
}

function renderGoals(goals, caption) {
  if (!goals?.length) return "";
  return goals.map((goal, index) => {
    const locals = (goal.locals ?? []).map(local => `<div><span class="local-name">${escapeHtml(local.name)}</span> : ${escapeHtml(local.formula)}</div>`).join("");
    const assumptions = (goal.assumptions ?? []).filter(item => !(goal.locals ?? []).some(local => local.formula === item))
      .map(item => `<div>· ${escapeHtml(item)}</div>`).join("");
    const context = locals + assumptions || '<div class="empty-context">No assumptions</div>';
    return `<div class="goal-card"><div class="goal-meta"><span>${escapeHtml(caption)}</span><code>${index + 1} of ${goals.length}</code></div><div class="context">${context}</div><div class="turnstile">${escapeHtml(goal.goal)}</div></div>`;
  }).join("");
}

function adjustLines(message, offset) {
  return String(message).replace(/\bline (\d+)\b/g, (whole, line) => {
    const adjusted = Number(line) - offset;
    return adjusted >= 1 ? `line ${adjusted}` : whole;
  });
}

function setStatus(kind, text) {
  const dot = $("statusDot");
  dot.className = `status-dot ${kind}`;
  $("statusText").textContent = text;
}

async function check({ silent = false } = {}) {
  if (!current || checking) return;
  checking = true;
  const serial = ++checkSerial;
  const entry = current;
  const proof = $("editor").value;
  progress.drafts[entry.id] = proof;
  saveProgress();
  const banned = forbiddenTacticUsed(entry.level, proof);
  if (banned) {
    checking = false;
    setStatus("warning", `${banned} is switched off here`);
    $("resultMeta").textContent = "";
    $("result").innerHTML = `<pre class="result-error">This level is by hand: ${escapeHtml(banned)} is switched off. Prove it from the lemmas named in the text.</pre>`;
    return;
  }
  setStatus("busy", "Checking…");
  $("check").disabled = true;
  const started = performance.now();
  let result;
  try {
    const name = fileName(entry);
    result = await requestWorkbench("check", { files: [{ name, source: levelSource(entry.world, entry.level, proof) }], activeFile: name });
  } catch (error) {
    result = { ok: false, message: error?.message || String(error) };
  } finally {
    checking = false;
    $("check").disabled = false;
  }
  if (serial !== checkSerial || current !== entry) return;
  const seconds = ((performance.now() - started) / 1000).toFixed(1);
  $("resultMeta").textContent = `${seconds}s`;
  const offset = bodyOffset(entry);
  if (!result?.ok) {
    setStatus("error", "Check failed");
    const trace = result?.trace;
    const goals = trace?.steps?.at(-1)?.after?.goals ?? trace?.initial?.goals;
    $("result").innerHTML = `<pre class="result-error">${escapeHtml(adjustLines(result?.message ?? "The checker reported no message.", offset))}</pre>${renderGoals(goals, "Goal where the proof stopped")}`;
    return;
  }
  const theorem = result.theorems?.[0];
  const sorries = theorem?.sorries ?? [];
  if (sorries.length === 0 && theorem) {
    setStatus("proven", `Checked in ${seconds}s`);
    const wasSolved = Boolean(progress.solved[entry.id]);
    progress.solved[entry.id] = true;
    saveProgress();
    renderWorlds();
    const index = levels.indexOf(entry);
    const next = levels[index + 1];
    $("result").innerHTML = `<div class="result-solved"><h2>Level complete</h2><p>The kernel checked <code>${escapeHtml(theorem.name.split(".").at(-1))}</code> from the axioms of set theory, with no sorry left.${wasSolved ? "" : " Nice."}</p>${
      next ? `<button type="button" id="advance" class="primary">Next: ${escapeHtml(next.level.title)} →</button>` : "<p>That was the last level. The rest of Cumulus is waiting in the Workbench.</p>"}</div>`;
    $("advance")?.addEventListener("click", () => openLevel(next.id));
    return;
  }
  setStatus("warning", silent ? "Ready" : `${sorries.length} ${sorries.length === 1 ? "sorry" : "sorries"} remain`);
  const steps = theorem?.steps ?? [];
  const holes = steps.filter(step => String(step.command ?? "").trim() === "sorry");
  const cards = holes.length
    ? holes.map(step => renderGoals(step.before?.goals?.slice(0, 1), `Goal at sorry, line ${Math.max(1, step.line - offset)}`)).join("")
    : renderGoals(steps.at(-1)?.after?.goals, "Remaining goal");
  $("result").innerHTML = cards || '<p class="muted">The proof checks but a sorry remains.</p>';
}

function showHint() {
  if (!current) return;
  const hints = current.level.hints ?? [];
  revealedHints = Math.min(hints.length, revealedHints + 1);
  const box = $("hints");
  box.hidden = revealedHints === 0;
  box.innerHTML = hints.slice(0, revealedHints).map((hint, index) => `<p><strong>Hint ${index + 1}.</strong> ${hint}</p>`).join("");
  $("hint").disabled = revealedHints >= hints.length;
}

function resetLevel() {
  if (!current) return;
  $("editor").value = current.level.starter;
  delete progress.drafts[current.id];
  saveProgress();
  updateWorkbenchLink();
  void check({ silent: true });
}

function handleEditorKey(event) {
  const editor = event.target;
  if ((event.metaKey || event.ctrlKey) && event.key === "Enter") { event.preventDefault(); void check(); return; }
  if (event.key === " " || event.key === "Tab" || event.key === "Enter") {
    const cursor = editor.selectionStart;
    if (cursor === editor.selectionEnd) {
      const completion = unicodeCompletionAt(editor.value, cursor);
      if (completion) {
        event.preventDefault();
        editor.setRangeText(completion.symbol, completion.start, completion.end, "end");
        editor.dispatchEvent(new Event("input"));
        return;
      }
    }
  }
  if (event.key === "Tab") {
    event.preventDefault();
    editor.setRangeText("  ", editor.selectionStart, editor.selectionEnd, "end");
    editor.dispatchEvent(new Event("input"));
  }
}

function wire() {
  $("check").addEventListener("click", () => void check());
  $("hint").addEventListener("click", showHint);
  $("reset").addEventListener("click", resetLevel);
  $("previous").addEventListener("click", () => { const index = levels.indexOf(current); if (index > 0) openLevel(levels[index - 1].id); });
  $("next").addEventListener("click", () => { const index = levels.indexOf(current); if (index < levels.length - 1) openLevel(levels[index + 1].id); });
  $("toggleWorlds").addEventListener("click", () => {
    const hidden = document.querySelector(".game").classList.toggle("worlds-hidden");
    $("toggleWorlds").setAttribute("aria-expanded", String(!hidden));
  });
  const editor = $("editor");
  editor.addEventListener("keydown", handleEditorKey);
  editor.addEventListener("input", () => {
    if (!current) return;
    progress.drafts[current.id] = editor.value;
    saveProgress();
    updateWorkbenchLink();
  });
  $("worlds").addEventListener("click", event => {
    const link = event.target.closest("a[data-level]");
    if (!link) return;
    event.preventDefault();
    openLevel(link.dataset.level);
  });
  window.addEventListener("hashchange", () => {
    const id = decodeURIComponent(location.hash.slice(1));
    if (byId.has(id) && current?.id !== id) openLevel(id, { pushHash: false });
  });
  document.addEventListener("keydown", event => {
    if ((event.metaKey || event.ctrlKey) && event.key === "Enter" && event.target !== editor) { event.preventDefault(); void check(); }
  });
}

wire();
setStatus("busy", "Local kernel starting…");
const requested = decodeURIComponent(location.hash.slice(1));
const firstOpen = levels.find(entry => !progress.solved[entry.id]) ?? levels[0];
openLevel(byId.has(requested) ? requested : firstOpen.id, { pushHash: false });
