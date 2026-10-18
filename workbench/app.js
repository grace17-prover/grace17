// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { resolveWorkbenchLink } from "./deep-links.js";
import { indexModuleDocuments, importSymbolAt } from "./module-navigation.js";
import { installLibrarySearch } from "./library-search-ui.js";
import { axiomAuditSummary, renderAxiomAudit, createAxiomAuditLoader, renderAxiomAuditAction } from "./axiom-audit.js";
import { declaredParameterNames, moduleNameOf, changedTextParts, checkedFileProofState, diagnosticIdentifier, diagnosticSpan, equivalenceClassNotationAtTextOffset, isFoundationInternalFile, kernelFitchOrder, localTypeAtTextOffset, migratePersistedCumulusFiles, notationAtTextOffset, notationForOperandTypes, notationOperandTypeAtTextOffset, notationTypeLabel, orderedPairNotationAtTextOffset, preferredProjectFile, proofDeclarationContext, proofMapSections, qualifiedSymbolCompletions, resolveSymbolCandidate, setNotationAtTextOffset, shouldRetainLastGoal, subscriptNotationAtTextOffset, tacticStepAtCursor, tacticTokenAtTextOffset, tokenAtTextOffset, unicodeCompletionAt, visibleTacticSteps, workspaceFilesForCheck } from "./editor-utils.js";
import { declarationHelpAtTextOffset, documentedTacticFamilies, helpInferenceRule, highlightGrace17, tacticGuideSections, tacticHelpEntries } from "./tactics-guide.js";
import { tacticReferenceNotes } from "./tactics-reference.js";
import { requestWorkbench } from "./worker-client.js";
import { standardLibrary } from "./generated/shims/standard-library.js";
import { version as WORKBENCH_VERSION } from "./generated/version.js";


const bundledModuleIndex = indexModuleDocuments(standardLibrary);
const monaco = globalThis.monaco;
const sourceHost = document.querySelector("#source");
const theoremSelect = document.querySelector("#theoremSelect");
const proofView = document.querySelector("#proofView");
const errorView = document.querySelector("#errorView");
const goalView = document.querySelector("#goalView");
const goalSymbolTooltip = document.querySelector("#goalSymbolTooltip");
let hoveredGoalSymbol;

configureGrace17Language();
monaco.languages.registerCompletionItemProvider("grace17", {
  triggerCharacters: ["."],
  provideCompletionItems(model, position) {
    const beforeCursor = model.getValueInRange({
      startLineNumber: position.lineNumber, startColumn: 1,
      endLineNumber: position.lineNumber, endColumn: position.column,
    });
    const resultNames = (resultFileBelongsHere(resultActiveFile) ? result?.symbols || [] : []).map(symbol => symbol.name);
    const completions = qualifiedSymbolCompletions([...new Set([...knownSymbolNames, ...resultNames])], beforeCursor);
    return { suggestions: completions.map(item => ({
      label: item.label,
      detail: item.canonical,
      kind: monaco.languages.CompletionItemKind.Reference,
      insertText: item.insertText,
      range: {
        startLineNumber: position.lineNumber, startColumn: item.replaceStart + 1,
        endLineNumber: position.lineNumber, endColumn: position.column,
      },
    })) };
  },
});
const editor = monaco.editor.create(sourceHost, {
  model: null,
  language: "grace17",
  theme: "grace17-dark",
  automaticLayout: true,
  fontFamily: 'ui-monospace, "SFMono-Regular", Consolas, monospace',
  fontSize: 13,
  lineHeight: 21,
  tabSize: 2,
  insertSpaces: true,
  detectIndentation: false,
  padding: { top: 12, bottom: 38 },
  minimap: { enabled: true, scale: 1, showSlider: "mouseover" },
  glyphMargin: true,
  folding: true,
  scrollBeyondLastLine: false,
  smoothScrolling: true,
  renderWhitespace: "selection",
  unicodeHighlight: { nonBasicASCII: false, ambiguousCharacters: false, invisibleCharacters: false },
  wordWrap: "off",
  ariaLabel: "Grace17 proof source",
});
const models = new Map();
const viewStates = new Map();
const diagnosticDecorations = editor.createDecorationsCollection();
const fileProofStates = new Map();
const theoremSorryCounts = new Map();
const qedTransitions = new Map();
const playedQedAnimations = new Set();
const expandedSorryTheorems = new Set();

// A small text-control compatibility layer keeps the proof-state and suggestion
// code independent of Monaco while editor input, selection and undo stay native.
const source = {
  get value() { return editor.getValue(); },
  set value(value) { editor.setValue(value); },
  get selectionStart() {
    const selection = editor.getSelection();
    return editor.getModel()?.getOffsetAt(selection.getStartPosition()) ?? 0;
  },
  get selectionEnd() {
    const selection = editor.getSelection();
    return editor.getModel()?.getOffsetAt(selection.getEndPosition()) ?? 0;
  },
  setRangeText(text, start, end, selectionMode = "end") {
    const model = editor.getModel();
    if (!model) return;
    const range = monaco.Range.fromPositions(model.getPositionAt(start), model.getPositionAt(end));
    editor.executeEdits("grace17", [{ range, text, forceMoveMarkers: true }]);
    const cursor = selectionMode === "select" ? start : start + text.length;
    const position = model.getPositionAt(cursor);
    editor.setPosition(position);
  },
  setSelectionRange(start, end) {
    const model = editor.getModel();
    if (!model) return;
    editor.setSelection(monaco.Range.fromPositions(model.getPositionAt(start), model.getPositionAt(end)));
  },
  focus() { editor.focus(); },
  dispatchEvent() {},
};

if ("serviceWorker" in navigator) {
  const localWorkbench = ["127.0.0.1", "localhost", "[::1]"].includes(location.hostname);
  if (localWorkbench) {
    navigator.serviceWorker.getRegistrations().then(registrations =>
      Promise.all(registrations.map(registration => registration.unregister()))).catch(() => {});
    if ("caches" in globalThis) caches.keys().then(names =>
      Promise.all(names.filter(name => name.startsWith("grace17-workbench-")).map(name => caches.delete(name)))).catch(() => {});
  } else {
    navigator.serviceWorker.register(new URL("./service-worker.js", import.meta.url)).catch(() => {});
    // The worker serves its cached build first, so the first visit after a
    // deploy runs the previous scripts and bundled library until the new
    // worker installs and takes control. A page the old worker was serving
    // then reloads once, keeping its link, so that everything it shows comes
    // from one build; a first-ever install has no old worker and no reload.
    const hadController = Boolean(navigator.serviceWorker.controller);
    navigator.serviceWorker.addEventListener("controllerchange", () => {
      if (!hadController || !navigator.serviceWorker.controller) return;
      offerUpdate("A new version of the Workbench is ready.");
    });
  }
}

// Leaving a stale build for real: the workspace is saved, this build's
// worker caches are dropped and the worker unregistered, every file of the
// shell and of the generated bundle is refetched past the HTTP cache (the
// host gives files a short freshness lifetime, so a plain reload can keep
// serving the old build), and only then does the page reload.
async function reloadOntoNewBuild() {
  try { persistWorkspace(); } catch { /* storage unavailable */ }
  try {
    const names = await caches.keys();
    await Promise.all(names.filter(name => name.startsWith("grace17-workbench-")).map(name => caches.delete(name)));
    const registrations = await navigator.serviceWorker.getRegistrations();
    await Promise.all(registrations.map(registration => registration.unregister()));
    const refetch = path => fetch(new URL(path, import.meta.url), { cache: "reload" }).catch(() => undefined);
    const shell = ["./", "./index.html", "./styles.css", "./bootstrap.js", "./app.js", "./editor-utils.js", "./module-navigation.js",
      "./axiom-audit.js", "./tactics-guide.js", "./tactics-reference.js", "./deep-links.js", "./library-search.js",
      "./library-search-worker.js", "./library-search-ui.js", "./worker-client.js", "./browser-worker.js", "./service-worker.js"];
    await Promise.all(shell.map(refetch));
    const manifest = await (await fetch(new URL("./generated/manifest.json", import.meta.url), { cache: "reload" })).json();
    await Promise.all((manifest.files || []).map(file => refetch(`./generated/${file}`)));
  } catch { /* the reload below still helps */ }
  location.reload();
}

// A new build is offered, never forced: the notice stays until the user
// reloads or dismisses it, and a reload keeps the workspace.
let updateNotice;
function offerUpdate(message) {
  if (updateNotice) { updateNotice.querySelector(".update-text").textContent = message; updateNotice.hidden = false; return; }
  updateNotice = document.createElement("div");
  updateNotice.className = "update-notice";
  updateNotice.setAttribute("role", "status");
  updateNotice.innerHTML = `<span class="update-text"></span><button type="button" class="action update-reload">Reload now</button><button type="button" class="action update-later">Later</button>`;
  updateNotice.querySelector(".update-text").textContent = message;
  updateNotice.querySelector(".update-reload").addEventListener("click", () => { reloadOntoNewBuild(); });
  updateNotice.querySelector(".update-later").addEventListener("click", () => { updateNotice.hidden = true; });
  document.body.append(updateNotice);
}

const WORKSPACE_SESSION_KEY = "grace17.workspaceSession";
const LEGACY_WORKSPACE_KEYS = [
  "grace17.files", "grace17.openFiles", "grace17.activeFile", "grace17.projectName",
  "grace17.filename", "grace17.source",
];

// A saved session is offered for recovery and is not reopened at startup. Browser storage
// outlives the local Node server, so reopening it automatically could combine
// a new Workbench with source views from an older Grace17 distribution.
let savedSession = readSavedSession();
for (const key of LEGACY_WORKSPACE_KEYS) localStorage.removeItem(key);

let files = [];
let openIds = [];
let activeId;
let projectName;
let result;
let resultActiveFile;
let knownSymbolNames = [];
let resultSources = new Map();
let selectedStep = 0;
const expandedProofSections = new Set();
const expandedProjectFolders = new Set();
let currentError = null;
const fileErrors = new Map();
let checkTimer;
let checkGeneration = 0;
let prepareGeneration = 0;
let resultRevision = 0;
let lastCursorGoalKey = "";
let cursorFrame;
let symbolCacheResult;
const symbolResolutionCache = new Map();

renderTabs();
if (activeId) {
  activateFile(activeId, false);
  // Dependency elaboration begins immediately and runs off the UI thread. The
  // subsequent check reuses the content-addressed checkpoint and admits only the
  // active editor leaf.
  prepareThenCheckActive();
} else showEmptyWorkspace();

editor.onDidChangeModelContent(() => {
  if (!activeFile()) return;
  // Invalidate an in-flight response immediately. The debounced replacement
  // check has not started yet, but its predecessor already describes old text.
  checkGeneration += 1;
  goalView.querySelectorAll("[data-axiom-audit]").forEach(action => action.remove());
  document.querySelector("#check").disabled = false;
  const wasDirty = activeFile().dirty;
  activeFile().source = source.value;
  activeFile().dirty = true;
  if (!wasDirty) renderTabs();
  persistWorkspace();
  currentError = null;
  fileErrors.delete(activeFile().name);
  fileProofStates.delete(activeFile().name);
  for (const theorem of result?.theorems || []) {
    if (resultFileBelongsHere(theorem.file)) playedQedAnimations.delete(theorem.name);
  }
  updateEditorDiagnostic();
  syncEditor();
  scheduleCheck();
});
editor.onDidChangeCursorPosition(scheduleCursorPosition);
editor.onDidChangeCursorSelection(scheduleCursorPosition);
editor.onMouseDown(event => {
  const browserEvent = event.event.browserEvent;
  if ((browserEvent.metaKey || browserEvent.ctrlKey) && event.target.position) {
    const offset = editor.getModel().getOffsetAt(event.target.position);
    const symbol = symbolAtOffset(offset);
    if (symbol) {
      browserEvent.preventDefault();
      goToDefinition(symbol);
    }
  }
});
editor.onKeyDown(event => {
  const delimiter = event.keyCode === monaco.KeyCode.Tab ? "Tab"
    : event.keyCode === monaco.KeyCode.Space ? " "
      : event.keyCode === monaco.KeyCode.Enter ? "Enter" : undefined;
  if (delimiter && !event.ctrlKey && !event.metaKey && source.selectionStart === source.selectionEnd) {
    const completion = unicodeCompletionAt(source.value, source.selectionStart);
    if (completion) {
      event.preventDefault();
      event.stopPropagation();
      const suffix = delimiter === " " ? " " : delimiter === "Enter" ? "\n" : "";
      source.setRangeText(completion.symbol + suffix, completion.start, completion.end, "end");
    }
  }
});
editor.addAction({
  id: "grace17.check",
  label: "Grace17: Check Proof",
  keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter],
  run: () => {
    clearTimeout(checkTimer);
    return check({ live: false });
  },
});
editor.addAction({
  id: "grace17.goToDefinition",
  label: "Grace17: Go to Definition",
  keybindings: [monaco.KeyCode.F12],
  contextMenuGroupId: "navigation",
  contextMenuOrder: 1,
  run: () => {
    const position = editor.getPosition();
    if (!position) return;
    const symbol = symbolAtOffset(editor.getModel().getOffsetAt(position));
    if (symbol?.line) goToDefinition(symbol);
  },
});
editor.addAction({
  id: "grace17.save",
  label: "Grace17: Save File",
  keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS],
  run: saveActiveFile,
});
editor.addAction({
  id: "grace17.help",
  label: "Grace17: Help",
  run: openTactics,
});
editor.addAction({
  id: "grace17.about",
  label: "Grace17: About",
  run: openAbout,
});

const loadAxiomAudit = createAxiomAuditLoader(requestWorkbench);
let axiomAuditGeneration = 0;
function auditPayload() { return { files: workspacePayload(), activeFile: activeFile()?.name }; }
async function openAxiomAudit(name) {
  if (!name && theoremSelect.value === "") return;
  name ||= result?.theorems?.[Number(theoremSelect.value)]?.name;
  if (!name) return;
  const generation = ++axiomAuditGeneration;
  const dialog = document.querySelector("#axiomAuditDialog");
  const body = document.querySelector("#axiomAuditBody");
  document.querySelector("#axiomAuditName").textContent = name;
  body.textContent = "Auditing the checked proof…";
  if (!dialog.open) dialog.showModal();
  const payload = auditPayload();
  try {
    const audit = await loadAxiomAudit(name, payload);
    if (generation !== axiomAuditGeneration || !dialog.open) return;
    if (JSON.stringify(payload) !== JSON.stringify(auditPayload())) {
      body.textContent = "The source changed. Reopen the audit for the current proof.";
      return;
    }
    body.innerHTML = renderAxiomAudit(audit);
  } catch (error) {
    if (generation === axiomAuditGeneration) body.textContent = `Audit unavailable: ${error.message}`;
  }
}
document.querySelector("#closeAxiomAudit").addEventListener("click", () => {
  axiomAuditGeneration++;
  document.querySelector("#axiomAuditDialog").close();
});
editor.addAction({ id: "grace17.axiomAudit", label: "Grace17: Axiom audit",
  run: (_editor, name) => openAxiomAudit(typeof name === "string" ? name : undefined) });

monaco.languages.registerHoverProvider("grace17", {
  async provideHover(model, position, token) {
    const symbol = symbolAtOffset(model.getOffsetAt(position));
    if (!symbol) return undefined;
    const contents = symbol.written
      ? [
        { value: `**${escapeMarkdown(symbol.token.text)}** · ${escapeMarkdown(symbol.kind)}` },
        { value: `\`${escapeMarkdown(symbol.written)}\` ⟼ \`${escapeMarkdown(symbol.elaborated)}\`` },
        ...(symbol.declaration ? [{ value: `\`\`\`${escapeMarkdown(symbol.declaration)}\`\`\`` }] : []),
        ...(symbol.module ? [{ value: escapeMarkdown(symbol.module) }] : []),
      ]
      : [
        { value: `**${escapeMarkdown(symbol.short)}** · ${escapeMarkdown(symbol.kind)}` },
        { value: `\`\`\`${escapeMarkdown(symbol.info)}\`\`\`` },
      ];
    if (symbol.line) contents.push({ value: `Command-click to open \`${escapeMarkdown(symbol.name)}\`.` });
    if (symbol.kind === "theorem") {
      const revision = model.getVersionId();
      const payload = auditPayload();
      try {
        const audit = await loadAxiomAudit(symbol.name, payload);
        if (token.isCancellationRequested || model.isDisposed() || model.getVersionId() !== revision ||
            JSON.stringify(payload) !== JSON.stringify(auditPayload())) return undefined;
        // The summary alone: the audit itself opens from the goal pane.
        contents.push({ value: escapeMarkdown(axiomAuditSummary(audit)) });
      } catch (error) {
        if (token.isCancellationRequested) return undefined;
        contents.push({ value: `Axiom audit unavailable: ${escapeMarkdown(error.message)}` });
      }
    }
    return {
      range: monaco.Range.fromPositions(model.getPositionAt(symbol.token.start), model.getPositionAt(symbol.token.end)),
      contents,
    };
  },
});

function dismissGoalSymbolTooltip() {
  goalSymbolTooltip.hidden = true;
  goalSymbolTooltip.removeAttribute("data-symbol-name");
  hoveredGoalSymbol = undefined;
}

function showGoalSymbolTooltip(target, event) {
  if (!target || !goalView.contains(target)) return dismissGoalSymbolTooltip();
  const semanticInfo = target.dataset.semanticInfo;
  const symbol = target.dataset.localSymbol === "true" ? {
    short: target.dataset.symbolShort,
    kind: target.dataset.symbolKind,
    info: semanticInfo,
  } : result?.symbols?.find(item => item.name === target.dataset.symbolName);
  if (!symbol) return dismissGoalSymbolTooltip();
  const notation = target.dataset.notation;
  const info = semanticInfo || symbol.info;
  const opens = symbol.line ? "Command-click to open the definition." : "";
  if (notation && target.dataset.written) {
    // A notation card: the token and its kind, the written form beside what
    // it elaborates to, the declaration itself, and the module.
    const footer = [target.dataset.module, opens].filter(Boolean).map(escapeHtml).join(" · ");
    goalSymbolTooltip.innerHTML = `<strong>${escapeHtml(notation)}<em>${escapeHtml(symbol.kind)}</em></strong>` +
      `<code class="map">${escapeHtml(target.dataset.written)}<span class="arrow">⟼</span>${escapeHtml(target.dataset.elaborated)}</code>` +
      (target.dataset.declaration ? `<code>${escapeHtml(target.dataset.declaration)}</code>` : "") +
      (footer ? `<small>${footer}</small>` : "");
  } else {
    goalSymbolTooltip.innerHTML = `<strong>${escapeHtml(notation ? `${notation} → ${symbol.short}` : symbol.short)}</strong><code>${escapeHtml(info)}</code><small>${escapeHtml(opens || symbol.kind)}</small>`;
  }
  goalSymbolTooltip.dataset.symbolName = target.dataset.symbolName;
  hoveredGoalSymbol = target;
  goalSymbolTooltip.hidden = false;
  positionGoalTooltip(event.clientX, event.clientY);
}

goalView.addEventListener("pointerover", event => {
  const target = event.target.closest?.(".semantic-symbol");
  if (target) showGoalSymbolTooltip(target, event);
});
goalView.addEventListener("pointermove", event => {
  const target = event.target.closest?.(".semantic-symbol");
  if (!target || !goalView.contains(target)) return dismissGoalSymbolTooltip();
  if (hoveredGoalSymbol !== target) showGoalSymbolTooltip(target, event);
  else if (!goalSymbolTooltip.hidden) positionGoalTooltip(event.clientX, event.clientY);
});
goalView.addEventListener("pointerout", event => {
  if (event.relatedTarget?.closest?.(".semantic-symbol") === event.target.closest?.(".semantic-symbol")) return;
  dismissGoalSymbolTooltip();
});
goalView.addEventListener("pointerleave", dismissGoalSymbolTooltip);
goalView.addEventListener("focusin", event => {
  const target = event.target.closest?.(".semantic-symbol");
  if (!target) return;
  const bounds = target.getBoundingClientRect();
  showGoalSymbolTooltip(target, { clientX: bounds.right, clientY: bounds.bottom });
});
goalView.addEventListener("focusout", dismissGoalSymbolTooltip);
goalView.addEventListener("click", event => {
  const auditAction = event.target.closest?.("[data-axiom-audit]");
  if (auditAction && goalView.contains(auditAction)) {
    event.preventDefault();
    openAxiomAudit(auditAction.dataset.axiomAudit);
    return;
  }
  const sorryToggle = event.target.closest?.("[data-toggle-sorries]");
  if (sorryToggle && goalView.contains(sorryToggle)) {
    event.preventDefault();
    const theorem = selectedTheorem();
    if (!theorem) return;
    if (expandedSorryTheorems.has(theorem.name)) expandedSorryTheorems.delete(theorem.name);
    else expandedSorryTheorems.add(theorem.name);
    renderTheorem();
    return;
  }
  const sorrySite = event.target.closest?.("[data-sorry-site]");
  if (sorrySite && goalView.contains(sorrySite)) {
    event.preventDefault();
    jumpToSorrySite(selectedTheorem(), Number(sorrySite.dataset.sorrySite));
    return;
  }
  if (!event.metaKey && !event.ctrlKey) return;
  const target = event.target.closest?.(".semantic-symbol");
  if (!target || !goalView.contains(target)) return;
  const symbol = result?.symbols?.find(item => item.name === target.dataset.symbolName);
  if (!symbol) return;
  event.preventDefault();
  dismissGoalSymbolTooltip();
  goToDefinition(symbol);
});
goalView.addEventListener("keydown", event => {
  if (event.key !== "Enter") return;
  const target = event.target.closest?.(".semantic-symbol.navigable");
  if (!target || !goalView.contains(target)) return;
  const symbol = result?.symbols?.find(item => item.name === target.dataset.symbolName);
  if (!symbol) return;
  event.preventDefault();
  dismissGoalSymbolTooltip();
  goToDefinition(symbol);
});

document.querySelector("#check").addEventListener("click", () => check({ live: false }));
document.querySelector("#tactics").addEventListener("click", openTactics);
document.querySelector("#closeTactics").addEventListener("click", closeTactics);
document.querySelector("#tacticsSearch").addEventListener("input", event => renderTacticsGuide(event.target.value));
document.querySelector("#tacticsDialog").addEventListener("click", event => {
  if (event.target === event.currentTarget) closeTactics();
});
document.querySelector("#tacticsDialog").addEventListener("close", () => editor.focus());
document.querySelector("#about").addEventListener("click", openAbout);
document.querySelector("#closeAbout").addEventListener("click", closeAbout);
document.querySelector("#aboutDialog").addEventListener("click", event => {
  if (event.target === event.currentTarget) closeAbout();
});
document.querySelector("#openFolder").addEventListener("click", openFolder);
document.querySelector("#openFile").addEventListener("click", () => document.querySelector("#filePicker").click());
document.querySelector("#saveFile").addEventListener("click", saveActiveFile);
document.querySelector("#newFile").addEventListener("click", newFile);
document.querySelector("#closeAllFiles").addEventListener("click", closeAllFiles);
document.querySelector("#emptyNew").addEventListener("click", newFile);
document.querySelector("#emptyBrowseCumulus").addEventListener("click", browseCumulus);
document.querySelector("#emptyOpen").addEventListener("click", () => document.querySelector("#filePicker").click());
document.querySelector("#emptyFolder").addEventListener("click", openFolder);
document.querySelector("#restoreSession").addEventListener("click", restoreSavedSession);
document.querySelector("#forgetSession").addEventListener("click", forgetSavedSession);
document.querySelector("#emptyVersion").textContent = WORKBENCH_VERSION;
const explorerInitiallyCollapsed = localStorage.getItem("grace17.explorerCollapsed") === "true";
document.querySelector("#projectExplorer").classList.toggle("collapsed", explorerInitiallyCollapsed);
document.querySelector("#toggleExplorer").textContent = explorerInitiallyCollapsed ? "›" : "‹";
document.querySelector("#toggleExplorer").setAttribute("aria-expanded", String(!explorerInitiallyCollapsed));
document.querySelector("#toggleExplorer").addEventListener("click", () => {
  const explorer = document.querySelector("#projectExplorer");
  const collapsed = explorer.classList.toggle("collapsed");
  const button = document.querySelector("#toggleExplorer");
  button.textContent = collapsed ? "›" : "‹";
  button.title = collapsed ? "Expand project files" : "Collapse project files";
  button.setAttribute("aria-label", button.title);
  button.setAttribute("aria-expanded", String(!collapsed));
  localStorage.setItem("grace17.explorerCollapsed", String(collapsed));
});
// A new Workbench boot always presents the proof state. Collapsing it is a
// session-level layout choice, while the independent edge rail guarantees that
// the pane can always be restored.
localStorage.removeItem("grace17.proofPaneCollapsed");
setProofPaneCollapsed(false);
document.querySelector("#toggleProofPane").addEventListener("click", () => {
  const workspace = document.querySelector(".workspace");
  setProofPaneCollapsed(!workspace.classList.contains("proof-collapsed"));
});
document.querySelector("#restoreProofPane").addEventListener("click", () => setProofPaneCollapsed(false));
configureWorkspaceDivider();
configureKernelDivider();
window.addEventListener("resize", clampKernelDrawerHeight);
document.querySelector("#filePicker").addEventListener("change", event => {
  openFiles([...event.target.files]);
  event.target.value = "";
});
document.querySelector(".editor-pane").addEventListener("dragover", event => {
  event.preventDefault();
  event.dataTransfer.dropEffect = "copy";
});
document.querySelector(".editor-pane").addEventListener("drop", event => {
  event.preventDefault();
  openFiles([...event.dataTransfer.files]);
});
document.querySelector("#editorError").addEventListener("click", jumpToDiagnostic);
theoremSelect.addEventListener("change", () => {
  selectedStep = 0;
  const theorem = selectedTheorem();
  renderTheorem();
  if (theorem && resultFileBelongsHere(theorem.file)) jumpToLine(theorem.lineStart);
});
document.querySelector("#kernelDrawer").addEventListener("toggle", event => {
  document.querySelector("#kernelResizeHandle").hidden = !event.currentTarget.open;
  if (event.currentTarget.open) {
    clampKernelDrawerHeight();
    void renderSelectedKernel();
  } else document.querySelector("#kernelView").innerHTML = "";
});

function makeId() {
  return globalThis.crypto?.randomUUID?.() ?? `file-${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

// Reference notes are Markdown paragraphs with inline code only.
function helpNoteHtml(note) {
  return escapeHtml(note).replace(/`([^`]+)`/g, "<code>$1</code>");
}

function renderTacticsGuide(query = "") {
  const needle = query.trim().toLocaleLowerCase();
  const sections = tacticGuideSections.map(section => ({
    ...section,
    entries: section.entries.filter(entry => !needle ||
      [section.title, section.intro, entry.syntax, entry.summary, entry.detail, entry.example, ...tacticReferenceNotes(entry.syntax)]
        .some(value => String(value || "").toLocaleLowerCase().includes(needle))),
  })).filter(section => section.entries.length);
  const count = sections.reduce((total, section) => total + section.entries.length, 0);
  document.querySelector("#tacticsCount").textContent = `${count} ${count === 1 ? "entry" : "entries"}`;
  const index = document.querySelector("#tacticsIndex");
  index.innerHTML = sections.map(section =>
    `<button data-tactic-section="${escapeHtml(section.id)}"><span>${escapeHtml(section.title)}</span><small>${section.entries.length}</small></button>`
  ).join("");
  const guide = document.querySelector("#tacticsGuide");
  guide.innerHTML = sections.length ? sections.map(section => `
    <section id="tactic-${escapeHtml(section.id)}" class="tactic-section">
      <header><h3>${escapeHtml(section.title)}</h3><p>${escapeHtml(section.intro)}</p></header>
      ${section.entries.map(entry => {
        const inference = helpInferenceRule(entry.syntax);
        const inferenceVariants = inference?.variants ?? (inference ? [inference] : []);
        const notes = tacticReferenceNotes(entry.syntax);
        return `<article class="tactic-entry">
        <code class="tactic-syntax">${escapeHtml(entry.syntax)}</code>
        <div><h4>${escapeHtml(entry.summary)}</h4><p>${escapeHtml(entry.detail)}</p>
        ${notes.length ? `<details class="help-more"><summary>More</summary>${notes.map(note => `<p>${helpNoteHtml(note)}</p>`).join("")}</details>` : ""}
        ${inferenceVariants.map(variant => `<div class="help-inference" aria-label="Natural deduction rule ${escapeHtml(variant.label)}">
          <div class="help-premises">${variant.premises.length ? variant.premises.map(premise => `<code>${escapeHtml(premise)}</code>`).join("") : `<span class="help-no-premises">no premises</span>`}</div>
          <div class="help-rule-line"><span>${escapeHtml(variant.label)}</span></div>
          <code class="help-conclusion">${escapeHtml(variant.conclusion)}</code>
          ${variant.side ? `<small>${escapeHtml(variant.side)}</small>` : ""}
        </div>`).join("")}
        ${entry.example ? `<pre class="help-example"><code>${highlightGrace17(entry.example)}</code></pre>` : ""}</div>
      </article>`;
      }).join("")}
    </section>`).join("") : `<p class="tactics-empty">No Help entry matches <code>${escapeHtml(query.trim())}</code>.</p>`;
  index.querySelectorAll("[data-tactic-section]").forEach(button => button.addEventListener("click", () => {
    guide.querySelector(`#tactic-${CSS.escape(button.dataset.tacticSection)}`)?.scrollIntoView({ block: "start", behavior: "smooth" });
  }));
}

function openTactics() {
  const dialog = document.querySelector("#tacticsDialog");
  renderTacticsGuide(document.querySelector("#tacticsSearch").value);
  if (typeof dialog.showModal === "function") dialog.showModal();
  else dialog.setAttribute("open", "");
  requestAnimationFrame(() => document.querySelector("#tacticsSearch").focus());
}

function closeTactics() {
  const dialog = document.querySelector("#tacticsDialog");
  if (typeof dialog.close === "function") dialog.close();
  else {
    dialog.removeAttribute("open");
    editor.focus();
  }
}

function openAbout() {
  const dialog = document.querySelector("#aboutDialog");
  document.querySelector("#aboutVersion").textContent = WORKBENCH_VERSION;
  if (typeof dialog.showModal === "function") dialog.showModal();
  else dialog.setAttribute("open", "");
}

function closeAbout() {
  const dialog = document.querySelector("#aboutDialog");
  if (typeof dialog.close === "function") dialog.close();
  else dialog.removeAttribute("open");
  editor.focus();
}

function setProofPaneCollapsed(collapsed) {
  const workspace = document.querySelector(".workspace");
  const button = document.querySelector("#toggleProofPane");
  workspace.classList.toggle("proof-collapsed", collapsed);
  button.textContent = "›";
  button.title = "Collapse proof state";
  button.setAttribute("aria-label", button.title);
  button.setAttribute("aria-expanded", String(!collapsed));
  requestAnimationFrame(() => editor.layout());
}

function configureWorkspaceDivider() {
  const workspace = document.querySelector(".workspace");
  const divider = document.querySelector("#workspaceDivider");
  const saved = Number(localStorage.getItem("grace17.editorWidth"));
  if (Number.isFinite(saved) && saved >= 25 && saved <= 75) workspace.style.setProperty("--editor-width", `${saved}%`);
  const resize = clientX => {
    const bounds = workspace.getBoundingClientRect();
    const percent = Math.min(75, Math.max(25, ((clientX - bounds.left) / bounds.width) * 100));
    workspace.style.setProperty("--editor-width", `${percent}%`);
    divider.setAttribute("aria-valuenow", String(Math.round(percent)));
    localStorage.setItem("grace17.editorWidth", String(percent));
  };
  divider.addEventListener("pointerdown", event => {
    divider.setPointerCapture(event.pointerId);
    divider.classList.add("dragging");
    resize(event.clientX);
  });
  divider.addEventListener("pointermove", event => {
    if (divider.hasPointerCapture(event.pointerId)) resize(event.clientX);
  });
  const release = event => {
    if (divider.hasPointerCapture(event.pointerId)) divider.releasePointerCapture(event.pointerId);
    divider.classList.remove("dragging");
  };
  divider.addEventListener("pointerup", release);
  divider.addEventListener("pointercancel", release);
  divider.addEventListener("keydown", event => {
    if (event.key !== "ArrowLeft" && event.key !== "ArrowRight") return;
    event.preventDefault();
    const current = Number.parseFloat(getComputedStyle(workspace).getPropertyValue("--editor-width")) || 54;
    const next = Math.min(75, Math.max(25, current + (event.key === "ArrowLeft" ? -2 : 2)));
    workspace.style.setProperty("--editor-width", `${next}%`);
    divider.setAttribute("aria-valuenow", String(next));
    localStorage.setItem("grace17.editorWidth", String(next));
  });
}

function configureKernelDivider() {
  const handle = document.querySelector("#kernelResizeHandle");
  const saved = Number(localStorage.getItem("grace17.kernelHeight"));
  if (Number.isFinite(saved) && saved >= 140) proofView.style.setProperty("--kernel-height", `${saved}px`);
  const resize = clientY => {
    const bounds = proofView.getBoundingClientRect();
    setKernelDrawerHeight(bounds.bottom - clientY);
  };
  handle.addEventListener("pointerdown", event => {
    handle.setPointerCapture(event.pointerId);
    handle.classList.add("dragging");
    resize(event.clientY);
  });
  handle.addEventListener("pointermove", event => {
    if (handle.hasPointerCapture(event.pointerId)) resize(event.clientY);
  });
  const release = event => {
    if (handle.hasPointerCapture(event.pointerId)) handle.releasePointerCapture(event.pointerId);
    handle.classList.remove("dragging");
  };
  handle.addEventListener("pointerup", release);
  handle.addEventListener("pointercancel", release);
  handle.addEventListener("dblclick", () => {
    localStorage.removeItem("grace17.kernelHeight");
    const height = Math.round(proofView.getBoundingClientRect().height * .42);
    proofView.style.setProperty("--kernel-height", `${height}px`);
    handle.setAttribute("aria-valuenow", String(height));
  });
  handle.addEventListener("keydown", event => {
    if (event.key !== "ArrowUp" && event.key !== "ArrowDown") return;
    event.preventDefault();
    const drawer = document.querySelector("#kernelDrawer");
    const current = drawer.getBoundingClientRect().height || proofView.getBoundingClientRect().height * .42;
    setKernelDrawerHeight(current + (event.key === "ArrowUp" ? 24 : -24));
  });
}

function setKernelDrawerHeight(requested) {
  const available = proofView.getBoundingClientRect().height;
  const maximum = Math.max(140, available - 126);
  const height = Math.round(Math.min(maximum, Math.max(140, requested)));
  proofView.style.setProperty("--kernel-height", `${height}px`);
  document.querySelector("#kernelResizeHandle").setAttribute("aria-valuenow", String(height));
  document.querySelector("#kernelResizeHandle").setAttribute("aria-valuemax", String(Math.round(maximum)));
  localStorage.setItem("grace17.kernelHeight", String(height));
}

function clampKernelDrawerHeight() {
  const drawer = document.querySelector("#kernelDrawer");
  if (!drawer.open) return;
  const configured = Number.parseFloat(getComputedStyle(proofView).getPropertyValue("--kernel-height"));
  setKernelDrawerHeight(Number.isFinite(configured) ? configured : proofView.getBoundingClientRect().height * .42);
}

function persistWorkspace() {
  if (!files.length && !projectName) return;
  const candidate = {
    version: WORKBENCH_VERSION,
    savedAt: Date.now(),
    projectName,
    activeId,
    openIds: [...openIds],
    files: files.map(({ handle, ...file }) => file.distribution === "cumulus" && !file.dirty
      ? { ...file, source: "" }
      : file),
  };
  try {
    localStorage.setItem(WORKSPACE_SESSION_KEY, JSON.stringify(candidate));
  } catch {
    // Editing must remain available when browser storage is disabled or full.
  }
}

function readSavedSession() {
  try {
    const current = JSON.parse(localStorage.getItem(WORKSPACE_SESSION_KEY) || "null");
    if (validSavedSession(current)) return current;
  } catch {}
  try {
    const legacyFiles = JSON.parse(localStorage.getItem("grace17.files") || "null");
    if (!Array.isArray(legacyFiles) || !legacyFiles.length) return undefined;
    const legacyOpenIds = JSON.parse(localStorage.getItem("grace17.openFiles") || "null");
    const candidate = {
      version: legacyFiles.find(file => file.openedIn)?.openedIn,
      projectName: localStorage.getItem("grace17.projectName") || undefined,
      activeId: localStorage.getItem("grace17.activeFile") || undefined,
      openIds: Array.isArray(legacyOpenIds) ? legacyOpenIds : legacyFiles.map(file => file.id),
      files: legacyFiles,
    };
    return validSavedSession(candidate) ? candidate : undefined;
  } catch {
    return undefined;
  }
}

function validSavedSession(session) {
  return Boolean(session && Array.isArray(session.files) && session.files.length
    && session.files.every(file => file.id && file.name && typeof file.source === "string")
    && Array.isArray(session.openIds));
}

function renderSavedSessionOffer() {
  const offer = document.querySelector("#savedSession");
  offer.hidden = !validSavedSession(savedSession);
  if (offer.hidden) return;
  const openCount = savedSession.openIds.length;
  const identity = savedSession.projectName || savedSession.files.find(file => file.id === savedSession.activeId)?.name || "Grace17 workspace";
  const version = savedSession.version ? ` · v${savedSession.version}` : "";
  document.querySelector("#savedSessionSummary").textContent = `${identity}${version} · ${savedSession.files.length} ${savedSession.files.length === 1 ? "file" : "files"} · ${openCount} ${openCount === 1 ? "open tab" : "open tabs"}`;
}

function forgetSavedSession() {
  clearSavedSessionRecovery();
  setStatus("Saved session forgotten");
}

function clearSavedSessionRecovery() {
  savedSession = undefined;
  localStorage.removeItem(WORKSPACE_SESSION_KEY);
  renderSavedSessionOffer();
}

function refreshCumulusDistribution() {
  const prefix = "lib/Grace/Cumulus/";
  migratePersistedCumulusFiles(files, standardLibrary, WORKBENCH_VERSION);
  const entries = [...standardLibrary].filter(([path]) => path === "lib/Grace/Cumulus.g17" || path.startsWith(prefix));
  const currentPaths = new Set(entries.map(([path]) => path));
  files.splice(0, files.length, ...files.filter(file =>
    file.distribution !== "cumulus" || file.dirty || currentPaths.has(file.sourceFile)));
  const bySourceFile = new Map(files.filter(file => file.sourceFile).map(file => [file.sourceFile, file]));
  return entries.map(([path, bundledSource]) => {
    const existing = bySourceFile.get(path);
    if (existing) {
      existing.distribution = "cumulus";
      existing.projectPath = path === "lib/Grace/Cumulus.g17" ? "Cumulus.g17" : path.slice(prefix.length);
      return existing;
    }
    const file = {
      id: makeId(), name: path,
      projectPath: path === "lib/Grace/Cumulus.g17" ? "Cumulus.g17" : path.slice(prefix.length),
      sourceFile: path, source: bundledSource, distribution: "cumulus", dirty: false,
      openedIn: WORKBENCH_VERSION,
    };
    files.push(file);
    return file;
  });
}

function restoreSavedSession() {
  if (!validSavedSession(savedSession)) return;
  const session = savedSession;
  savedSession = undefined;
  disposeModels();
  files = session.files.map(file => ({ ...file }));
  projectName = session.projectName;
  if (projectName?.startsWith("Cumulus ") || files.some(file => file.distribution === "cumulus")) {
    refreshCumulusDistribution();
    projectName = `Cumulus ${WORKBENCH_VERSION}`;
  }
  const available = new Set(files.map(file => file.id));
  openIds = session.openIds.filter(id => available.has(id));
  activeId = available.has(session.activeId) ? session.activeId : openIds[0];
  if (activeId && !openIds.includes(activeId)) openIds.unshift(activeId);
  expandedProjectFolders.clear();
  result = undefined;
  resultActiveFile = undefined;
  currentError = null;
  fileErrors.clear();
  if (activeId) {
    activateFile(activeId, false);
    prepareThenCheckActive();
  } else {
    persistWorkspace();
    showEmptyWorkspace();
  }
  setStatus(`Restored ${projectName || "saved session"}`);
}

function activeFile() { return files.find(file => file.id === activeId); }
function fileResultNames(file = activeFile()) {
  return new Set(file ? [file.name, file.sourceFile].filter(Boolean) : []);
}
function resultFileBelongsHere(name, file = activeFile()) { return Boolean(name && fileResultNames(file).has(name)); }
function workspacePayload() { return workspaceFilesForCheck(files, activeId, WORKBENCH_VERSION); }

function recordQEDTransitions(data) {
  for (const theorem of data.theorems || []) {
    const count = theorem.sorries?.length ?? 0;
    const previous = theoremSorryCounts.get(theorem.name);
    qedTransitions.set(theorem.name, previous > 0 && count === 0
      ? { kind: "upgrade", previous }
      : { kind: "complete", previous });
    theoremSorryCounts.set(theorem.name, count);
  }
}

function updateFileProofStates(data) {
  for (const name of data.checkedFiles || []) {
    const summary = data.files?.find(file => file.name === name);
    const state = checkedFileProofState(summary);
    if (state) fileProofStates.set(name, state);
    else fileProofStates.delete(name);
  }
}

function rollupMark(state, label) {
  if (!state) return "";
  const sorry = state === "sorry";
  return `<svg class="rollup-mark ${state}" viewBox="0 0 20 20" role="img" aria-label="${escapeHtml(label)}"><g transform="translate(-51.84 -11.39) scale(.214)"><path class="rollup-arc" d="M 310 77.92 A 28 28 0 1 0 310 121.92"/></g><path class="rollup-check" d="M6 10.2L9.2 13L15.8 7"${sorry ? ' pathLength="13" stroke-dasharray="3 2" stroke-dashoffset="0"' : ""}/></svg>`;
}

function treeProofState(node) {
  const states = [
    ...node.files.map(({ file }) => fileProofStates.get(file.name)),
    ...[...node.folders.values()].map(treeProofState),
  ];
  if (states.includes("sorry")) return "sorry";
  return states.length && states.every(state => state === "proven") ? "proven" : undefined;
}

function modelFor(file) {
  let model = models.get(file.id);
  if (!model) {
    model = monaco.editor.createModel(file.source, "grace17", monaco.Uri.parse(`inmemory://grace17/${encodeURIComponent(file.id)}/${encodeURIComponent(file.name)}`));
    models.set(file.id, model);
  }
  return model;
}

function disposeModels() {
  for (const model of models.values()) model.dispose();
  models.clear();
  viewStates.clear();
}

function renderTabs() {
  const openFiles = openIds.map(id => files.find(file => file.id === id)).filter(Boolean);
  document.querySelector("#fileTabs").innerHTML = openFiles.map(file => {
    const hasError = fileErrors.has(file.name);
    const proofState = fileProofStates.get(file.name);
    const rollup = rollupMark(proofState, proofState === "sorry" ? "File contains sorry" : "File fully proven");
    return `<button class="file-tab ${file.id === activeId ? "active" : ""} ${hasError ? "error" : ""} ${file.dirty ? "dirty" : ""}" role="tab" aria-selected="${file.id === activeId}" data-file="${file.id}" title="${escapeHtml(file.name)}${file.dirty ? " · unsaved changes" : ""}"><span class="tab-name">${escapeHtml(file.name)}</span>${rollup}<span class="tab-close" data-close="${file.id}" aria-label="Close ${escapeHtml(file.name)}">×</span></button>`;
  }).join("");
  document.querySelectorAll(".file-tab").forEach(tab => tab.addEventListener("click", event => {
    const closing = event.target.closest("[data-close]");
    if (closing) closeFile(closing.dataset.close);
    else {
      activateFile(tab.dataset.file);
      check({ live: true });
    }
  }));
  document.querySelector("#closeAllFiles").hidden = openFiles.length === 0;
  renderProjectExplorer();
}

function renderProjectExplorer() {
  const explorer = document.querySelector("#projectExplorer");
  explorer.hidden = !projectName;
  if (!projectName) return;
  document.querySelector("#projectName").textContent = projectName;
  const buildTree = selected => {
    const root = { folders: new Map(), files: [] };
    for (const file of [...selected].sort((left, right) => (left.projectPath || left.name).localeCompare(right.projectPath || right.name))) {
    const parts = (file.projectPath || file.name).split("/").filter(Boolean);
    let node = root;
    for (const folder of parts.slice(0, -1)) {
      if (!node.folders.has(folder)) node.folders.set(folder, { folders: new Map(), files: [] });
      node = node.folders.get(folder);
    }
    node.files.push({ file, label: parts.at(-1) || file.name });
    }
    return root;
  };
  const renderNode = (node, parentPath = "") => {
    const folders = [...node.folders].map(([name, child]) => {
      const path = parentPath ? `${parentPath}/${name}` : name;
      const proofState = treeProofState(child);
      const rollup = rollupMark(proofState, proofState === "sorry" ? "Module contains sorry" : "Module fully proven");
      const open = expandedProjectFolders.has(path) ? " open" : "";
      return `<details data-project-folder="${escapeHtml(path)}"${open}><summary><span>${escapeHtml(name)}</span>${rollup}</summary><div class="project-tree-children">${renderNode(child, path)}</div></details>`;
    }).join("");
    const leaves = node.files.map(({ file, label }) => {
      const proofState = fileProofStates.get(file.name);
      const rollup = rollupMark(proofState, proofState === "sorry" ? "File contains sorry" : "File fully proven");
      return `<button class="project-file ${file.id === activeId ? "active" : ""} ${fileErrors.has(file.name) ? "error" : ""}" data-project-file="${file.id}" title="${escapeHtml(file.name)}"><span>${escapeHtml(label)}</span>${rollup}</button>`;
    }).join("");
    return folders + leaves;
  };
  const visibleFiles = projectName === `Cumulus ${WORKBENCH_VERSION}` ? files.filter(file => file.distribution === "cumulus") : files;
  const ordinary = visibleFiles.filter(file => !isFoundationInternalFile(file.name));
  const internals = visibleFiles.filter(file => isFoundationInternalFile(file.name));
  const internalOpen = isFoundationInternalFile(activeFile()?.name) ? " open" : "";
  const internalTree = internals.length
    ? `<details class="project-internals"${internalOpen}><summary>Foundation internals</summary><div class="project-tree-children">${renderNode(buildTree(internals), "Foundation internals")}</div></details>`
    : "";
  document.querySelector("#projectFiles").innerHTML = renderNode(buildTree(ordinary)) + internalTree;
  document.querySelectorAll("[data-project-folder]").forEach(folder => folder.addEventListener("toggle", () => {
    if (folder.open) expandedProjectFolders.add(folder.dataset.projectFolder);
    else expandedProjectFolders.delete(folder.dataset.projectFolder);
  }));
  document.querySelectorAll("[data-project-file]").forEach(button => button.addEventListener("click", () => {
    activateFile(button.dataset.projectFile);
    check({ live: true });
  }));
}

function activateFile(id, focus = true) {
  const file = files.find(item => item.id === id);
  if (!file) return;
  if (activeId !== id) {
    // Async responses own the buffer that launched them. Moving to another
    // buffer invalidates both checks and dependency preparation immediately.
    checkGeneration += 1;
    prepareGeneration += 1;
    knownSymbolNames = [];
  }
  if (!openIds.includes(id)) openIds.push(id);
  if (editor.getModel() && activeId && activeId !== id) viewStates.set(activeId, editor.saveViewState());
  activeId = id;
  const parts = (file.projectPath || "").split("/").filter(Boolean).slice(0, -1);
  for (let length = 1; length <= parts.length; length += 1) {
    expandedProjectFolders.add(parts.slice(0, length).join("/"));
  }
  document.querySelector("#source").hidden = false;
  document.querySelector("#emptyWorkspace").hidden = true;
  document.querySelector(".proof-pane").classList.remove("workspace-empty");
  document.querySelector("#check").disabled = false;
  document.querySelector("#saveFile").disabled = false;
  editor.setModel(modelFor(file));
  const viewState = viewStates.get(id);
  if (viewState) editor.restoreViewState(viewState);
  document.querySelector("#fileName").textContent = file.name;
  persistWorkspace();
  renderTabs();
  updateEditorDiagnostic();
  syncEditor();
  populateTheorems();
  syncGoalToCursor();
  if (focus) source.focus();
}

function closeFileNow(id) {
  const index = openIds.indexOf(id);
  if (index < 0) return;
  openIds.splice(index, 1);
  if (activeId === id) activeId = openIds[Math.min(index, openIds.length - 1)];
  if (!openIds.length) return showEmptyWorkspace();
  persistWorkspace();
  activateFile(activeId, false);
  scheduleCheck(0);
}

async function closeFile(id) {
  const file = files.find(item => item.id === id);
  if (!file || !await confirmFileClose(file)) return;
  closeFileNow(id);
}

async function closeAllFiles() {
  const openFiles = openIds.map(id => files.find(file => file.id === id)).filter(Boolean);
  for (const file of openFiles) {
    if (!await confirmFileClose(file)) return;
  }
  openIds = [];
  showEmptyWorkspace();
  clearSavedSessionRecovery();
}

function browseCumulus() {
  const previousActive = activeFile();
  const distributionFiles = refreshCumulusDistribution();
  const availableIds = new Set(files.map(file => file.id));
  openIds = openIds.filter(id => availableIds.has(id));
  let replacedActive = false;
  if (activeId && !availableIds.has(activeId)) {
    activeId = files.find(file => file.sourceFile === previousActive?.sourceFile)?.id
      || files.find(file => file.projectPath === previousActive?.projectPath)?.id
      || openIds[0];
    if (activeId && !openIds.includes(activeId)) openIds.push(activeId);
    replacedActive = true;
  }
  if (!distributionFiles.length) return setStatus("The bundled Cumulus distribution is unavailable", "error");
  projectName = `Cumulus ${WORKBENCH_VERSION}`;
  expandedProjectFolders.clear();
  const explorer = document.querySelector("#projectExplorer");
  explorer.classList.remove("collapsed");
  const explorerToggle = document.querySelector("#toggleExplorer");
  explorerToggle.textContent = "‹";
  explorerToggle.title = "Collapse project files";
  explorerToggle.setAttribute("aria-label", explorerToggle.title);
  explorerToggle.setAttribute("aria-expanded", "true");
  localStorage.setItem("grace17.explorerCollapsed", "false");
  persistWorkspace();
  renderProjectExplorer();
  if (replacedActive && activeId) activateFile(activeId, false);
  setStatus(`Cumulus ${WORKBENCH_VERSION} · choose from ${distributionFiles.length} files`);
}

function showEmptyWorkspace() {
  clearTimeout(checkTimer);
  checkGeneration += 1;
  activeId = undefined;
  currentError = null;
  editor.setModel(null);
  dismissGoalSymbolTooltip();
  document.querySelector("#source").hidden = true;
  document.querySelector("#emptyWorkspace").hidden = false;
  document.querySelector(".proof-pane").classList.add("workspace-empty");
  document.querySelector("#editorError").hidden = true;
  document.querySelector("#fileName").textContent = "No file open";
  document.querySelector("#cursor").textContent = "";
  document.querySelector("#check").disabled = true;
  document.querySelector("#saveFile").disabled = true;
  proofView.hidden = true;
  errorView.hidden = true;
  goalView.innerHTML = "";
  document.querySelector("#kernelView").innerHTML = "";
  document.querySelector("#kernelSummary").textContent = "";
  theoremSelect.innerHTML = '<option value="">No proof selected</option>';
  document.querySelector("#summary").textContent = "";
  setStatus("Workspace empty");
  persistWorkspace();
  renderSavedSessionOffer();
  renderTabs();
}

function newFile() {
  let number = 1;
  while (files.some(file => file.name === `Scratch${number}.g17`)) number += 1;
  const name = `Scratch${number}.g17`;
  const file = { id: makeId(), name, dirty: true, openedIn: WORKBENCH_VERSION, source: `module Scratch${number}
import Grace.Cumulus.Main

` };
  files.push(file);
  openIds.push(file.id);
  activateFile(file.id);
  scheduleCheck(0);
}

async function openFiles(opened) {
  if (!opened.length) return;
  let nextActiveId = activeId;
  for (const diskFile of opened) {
    const name = diskFile.webkitRelativePath || diskFile.name;
    const text = await diskFile.text();
    const existing = files.find(file => file.name === name);
    fileErrors.delete(name);
    if (existing) {
      Object.assign(existing, { source: text, dirty: false, openedIn: WORKBENCH_VERSION });
      fileProofStates.delete(name);
      models.get(existing.id)?.dispose();
      models.delete(existing.id);
    }
    else files.push({ id: makeId(), name, source: text, dirty: false, openedIn: WORKBENCH_VERSION });
    nextActiveId = (existing ?? files.at(-1)).id;
    if (!openIds.includes(nextActiveId)) openIds.push(nextActiveId);
  }
  currentError = null;
  activateFile(nextActiveId);
  setStatus(`${opened.length} ${opened.length === 1 ? "file" : "files"} opened`);
  scheduleCheck(0);
}

async function openFolder() {
  if (!("showDirectoryPicker" in window)) {
    document.querySelector("#filePicker").click();
    setStatus("Folder access is unavailable · choose .g17 files instead", "error");
    return;
  }
  try {
    const directory = await window.showDirectoryPicker({ mode: "readwrite", id: "grace17-project" });
    const opened = await readGraceDirectory(directory);
    if (!opened.length) return setStatus("No .g17 files found", "error");
    if (opened.length > 256 || opened.reduce((size, file) => size + file.source.length, 0) > 5_000_000) {
      throw new Error("Grace17 project exceeds the browser workspace limit");
    }
    disposeModels();
    files = opened;
    const initial = preferredProjectFile(files);
    openIds = [initial.id];
    activeId = initial.id;
    projectName = directory.name;
    expandedProjectFolders.clear();
    result = undefined;
    resultActiveFile = undefined;
    currentError = null;
    fileErrors.clear();
    persistWorkspace();
    activateFile(activeId, false);
    setStatus(`Opened ${directory.name} · ${files.length} files`);
    scheduleCheck(0);
  } catch (error) {
    if (error?.name !== "AbortError") setStatus(error.message || "Could not open folder", "error");
  }
}

async function readGraceDirectory(directory, prefix = "") {
  const opened = [];
  for await (const [name, handle] of directory.entries()) {
    if (name.startsWith(".")) continue;
    const path = prefix ? `${prefix}/${name}` : name;
    if (handle.kind === "directory") opened.push(...await readGraceDirectory(handle, path));
    else if (name.endsWith(".g17")) {
      const diskFile = await handle.getFile();
      opened.push({ id: makeId(), name: path, source: await diskFile.text(), handle, dirty: false, openedIn: WORKBENCH_VERSION });
    }
  }
  return opened;
}

function askUnsavedFile(file) {
  const dialog = document.querySelector("#unsavedDialog");
  document.querySelector("#unsavedFileName").textContent = file.name;
  dialog.returnValue = "cancel";
  return new Promise(resolve => {
    dialog.addEventListener("close", () => resolve(dialog.returnValue || "cancel"), { once: true });
    dialog.showModal();
  });
}

async function confirmFileClose(file) {
  if (!file.dirty) return true;
  const choice = await askUnsavedFile(file);
  if (choice === "discard") return true;
  if (choice !== "save") return false;
  return saveFile(file);
}

async function saveFile(file) {
  try {
    let handle = file.handle;
    if (!handle && "showSaveFilePicker" in window) {
      handle = await window.showSaveFilePicker({
        id: "grace17-source",
        suggestedName: file.name.split("/").at(-1),
        types: [{ description: "Grace17 source", accept: { "text/plain": [".g17"] } }],
      });
      file.handle = handle;
    }
    if (handle) {
      const writable = await handle.createWritable();
      await writable.write(file.source);
      await writable.close();
      file.dirty = false;
      persistWorkspace();
      renderTabs();
      setStatus(`Saved ${file.name} · local file`);
      return true;
    }
    const link = document.createElement("a");
    link.href = URL.createObjectURL(new Blob([file.source], { type: "text/plain" }));
    link.download = file.name.split("/").at(-1);
    link.click();
    URL.revokeObjectURL(link.href);
    file.dirty = false;
    persistWorkspace();
    renderTabs();
    setStatus(`Downloaded ${link.download}`);
    return true;
  } catch (error) {
    if (error?.name !== "AbortError") setStatus(error.message || "Could not save file", "error");
    return false;
  }
}

async function saveActiveFile() {
  const file = activeFile();
  if (file) await saveFile(file);
}

function escapeHtml(value) {
  return String(value).replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;");
}

function syncEditor() {
  updateEditorMarkers();
  cursorPosition();
}

function cursorLocation() {
  const position = editor.getPosition() || { lineNumber: 1, column: 1 };
  return { line: position.lineNumber, column: position.column };
}
function cursorLine() { return cursorLocation().line; }
function scheduleCursorPosition() {
  if (cursorFrame !== undefined) return;
  cursorFrame = requestAnimationFrame(() => {
    cursorFrame = undefined;
    cursorPosition();
  });
}
function cursorPosition() {
  if (!activeFile() || !editor.getModel()) return;
  const location = cursorLocation();
  document.querySelector("#cursor").textContent = `Ln ${location.line}, Col ${location.column}`;
  syncGoalToCursor(location.line, location.column);
}

function setStatus(text, kind = "") {
  document.querySelector(".status").className = `status ${kind}`;
  document.querySelector("#statusText").textContent = text;
  document.querySelector("#statusDot").className = `status-dot ${kind}`;
}

function scheduleCheck(delay = 480) {
  clearTimeout(checkTimer);
  checkTimer = setTimeout(() => check({ live: true }), delay);
}

function prepareActiveDependencies() {
  const file = activeFile();
  if (!file) return Promise.resolve();
  const generation = ++prepareGeneration;
  const fileId = file.id;
  const sourceRevision = file.source;
  return requestWorkbench("prepare", {
    files: workspacePayload(), activeFile: file.name,
  }).then(data => {
    if (generation === prepareGeneration && activeFile()?.id === fileId && activeFile()?.source === sourceRevision && data?.symbols) {
      knownSymbolNames = data.symbols;
    }
    return data;
  }).catch(() => undefined);
}

function prepareThenCheckActive() {
  const file = activeFile();
  if (!file) return Promise.resolve();
  const fileId = file.id;
  const sourceRevision = file.source;
  return prepareActiveDependencies().finally(() => {
    if (activeFile()?.id === fileId && activeFile()?.source === sourceRevision) check({ live: true });
  });
}

async function check({ live = false } = {}) {
  if (!activeFile()) return showEmptyWorkspace();
  const generation = ++checkGeneration;
  const checkedFile = activeFile().name;
  const payloadFiles = workspacePayload();
  setStatus(live ? "Checking as you type…" : "Checking…", "busy");
  if (!live) document.querySelector("#check").disabled = true;
  try {
    const data = await requestWorkbench("check", {
      files: payloadFiles, activeFile: checkedFile,
    });
    if (generation !== checkGeneration) return;
    if (!data.ok) {
      data.file ||= checkedFile;
      return showError(data, { sources: new Map(payloadFiles.map(file => [file.name, file.source])) });
    }
    result = data;
    resultActiveFile = checkedFile;
    resultRevision += 1;
    lastCursorGoalKey = "";
    knownSymbolNames = data.symbols?.map(symbol => symbol.name) ?? knownSymbolNames;
    recordQEDTransitions(data);
    updateFileProofStates(data);
    resultSources = new Map(payloadFiles.map(file => [file.name, file.source]));
    currentError = null;
    (data.checkedFiles || [checkedFile]).forEach(file => fileErrors.delete(file));
    updateEditorDiagnostic();
    renderTabs();
    errorView.hidden = true;
    proofView.hidden = false;
    populateTheorems();
    syncGoalToCursor();
    const sorryCount = data.sorries?.length ?? 0;
    const hasProofs = Boolean(data.theorems?.length);
    const status = hasProofs ? (sorryCount ? `${sorryCount} ${sorryCount === 1 ? "sorry" : "sorries"}` : "goals = ∅")
      : data.context === "bootstrap" ? "bootstrap checked" : "workspace checked";
    setStatus(`${status} · ${data.milliseconds} ms`, sorryCount ? "warning" : hasProofs ? "proven" : "");
  } catch (error) {
    if (generation === checkGeneration) showError({ kind: "network", file: checkedFile, message: error.message });
  } finally {
    if (!live && generation === checkGeneration) document.querySelector("#check").disabled = false;
  }
}

function errorBelongsHere() { return currentError && activeFile() && (!currentError.file || resultFileBelongsHere(currentError.file)); }

function updateEditorDiagnostic() {
  const editorError = document.querySelector("#editorError");
  if (!errorBelongsHere()) { editorError.hidden = true; updateEditorMarkers(); return; }
  const location = diagnosticLocation(currentError);
  const message = diagnosticMessageHtml(currentError.message || "Unknown error");
  editorError.hidden = false;
  editorError.innerHTML = `<span class="diagnostic-square" aria-hidden="true"></span><code class="diagnostic-location">${escapeHtml(location)}</code><span class="diagnostic-message">${message}</span><span class="diagnostic-show">show <span aria-hidden="true">▸</span></span>`;
  updateEditorMarkers();
}

function diagnosticMessageHtml(message) {
  const identifier = diagnosticIdentifier(message);
  if (!identifier) return escapeHtml(message);
  const start = message.lastIndexOf(identifier);
  if (start < 0) return escapeHtml(message);
  return `${escapeHtml(message.slice(0, start))}<code class="diagnostic-chip">${escapeHtml(identifier)}</code>${escapeHtml(message.slice(start + identifier.length))}`;
}

function inferredDiagnosticRange(error) {
  const model = editor.getModel();
  const line = Math.min(Math.max(1, error.line || 1), model?.getLineCount() || 1);
  const text = model?.getLineContent(line) || "";
  return { line, ...diagnosticSpan(text, error.message, error.column) };
}

function diagnosticLocation(error) {
  const range = inferredDiagnosticRange(error);
  return `${error.file || activeFile().name}:${range.line}:${range.startColumn}`;
}

function updateEditorMarkers() {
  const model = editor.getModel();
  if (!model) return;
  const sorryDecorations = activeSorrySites().flatMap((site, index, sites) => {
    const range = sorryKeywordRange(model, site, sites);
    if (!range) return [];
    return [
      { range: new monaco.Range(range.line, 1, range.line, 1), options: { isWholeLine: true, glyphMarginClassName: "sorry-gutter-dot", glyphMarginHoverMessage: { value: "Proof obligation admitted with `sorry`." } } },
      { range: new monaco.Range(range.line, range.startColumn, range.line, range.endColumn), options: { inlineClassName: "sorry-span", hoverMessage: { value: "Proof obligation admitted with `sorry`." } } },
    ];
  });
  if (!errorBelongsHere()) {
    diagnosticDecorations.set(sorryDecorations);
    return monaco.editor.setModelMarkers(model, "grace17", []);
  }
  const { line, startColumn, endColumn } = inferredDiagnosticRange(currentError);
  monaco.editor.setModelMarkers(model, "grace17", [{
    severity: monaco.MarkerSeverity.Error,
    message: currentError.message || "Unknown error",
    source: `Grace17 ${currentError.kind || "error"}`,
    startLineNumber: line,
    startColumn,
    endLineNumber: line,
    endColumn,
  }]);
  diagnosticDecorations.set([...sorryDecorations,
    { range: new monaco.Range(line, 1, line, 1), options: { isWholeLine: true, className: "diagnostic-line", glyphMarginClassName: "diagnostic-gutter-dot" } },
    { range: new monaco.Range(line, startColumn, line, endColumn), options: { inlineClassName: "diagnostic-span" } },
  ]);
}

function activeSorrySites() {
  const file = activeFile();
  if (!file) return [];
  const identities = [...fileResultNames(file)];
  const checkedSource = identities.map(name => resultSources.get(name)).find(source => source !== undefined)
    ?? result?.documents?.find(document => identities.includes(document.file))?.source;
  if (checkedSource !== file.source) return [];
  return (result?.sorries || []).filter(site => identities.includes(site.file));
}

function sorryKeywordRange(model, site, sites) {
  const line = Math.min(Math.max(1, site.line || 1), model.getLineCount());
  const matches = [...model.getLineContent(line).matchAll(/\bsorry\b/g)];
  const occurrence = sites.slice(0, sites.indexOf(site)).filter(other => other.line === site.line).length;
  const match = matches[occurrence] || matches[0];
  if (!match) return undefined;
  return { line, startColumn: match.index + 1, endColumn: match.index + match[0].length + 1 };
}

function showError(error, { focus = false, sources } = {}) {
  let workingState = false;
  currentError = error;
  if (error.file) {
    fileErrors.set(error.file, error);
    fileProofStates.delete(error.file);
  }
  renderTabs();
  updateEditorDiagnostic();
  syncEditor();
  if (error.trace) {
    workingState = true;
    if (sources) resultSources = sources;
    const failedFile = files.find(file => fileResultNames(file).has(error.file || activeFile().name)) || activeFile();
    const context = proofDeclarationContext(failedFile.source, error.line);
    errorView.hidden = true;
    proofView.hidden = false;
    result = { theorems: [{
      name: context?.name || "Incomplete proof",
      file: failedFile.name,
      lineStart: context?.lineStart || 1,
      lineEnd: context?.lineEnd || Number.MAX_SAFE_INTEGER,
      statement: context?.statement || "Proof incomplete",
      proofNodes: 0,
      judgments: 0,
      dependencies: { axioms: [], theorems: [], definitions: [] },
      proofMap: error.trace.proofMap ?? [],
      initial: error.trace.initial,
      steps: error.trace.steps,
      kernel: [],
    }] };
    resultActiveFile = failedFile.name;
    resultRevision += 1;
    lastCursorGoalKey = "";
    theoremSelect.innerHTML = `<option value="0">${escapeHtml(result.theorems[0].name)}</option>`;
    theoremSelect.value = "0";
    selectedStep = error.trace.steps.length;
    renderTheorem();
  } else if (shouldRetainLastGoal({
    hasTrace: Boolean(error.trace), hasResult: Boolean(result), errorBelongsToFile: Boolean(errorBelongsHere()),
    theoremCount: fileTheoremIndices().length,
  })) {
    workingState = true;
    // A malformed token or half-written theorem header has no partial tactic
    // trace. Keep the last successfully elaborated proof state visible while
    // presenting the new diagnostic as stale-source information.
    errorView.hidden = true;
    proofView.hidden = false;
    renderTheorem();
  } else {
    proofView.hidden = true;
    errorView.hidden = false;
    errorView.innerHTML = `<strong>${diagnosticMessageHtml(error.message || "Unknown error")}</strong><code>${escapeHtml(diagnosticLocation(error))}</code>`;
  }
  setStatus(workingState ? "Proof in progress" : "Check failed", workingState ? "busy" : "error");
  if (focus && errorBelongsHere() && error.line) jumpToLine(error.line);
}

function jumpToLine(line) {
  if (!line) return;
  const model = editor.getModel();
  const safeLine = Math.min(Math.max(1, line), model.getLineCount());
  editor.setSelection(new monaco.Range(safeLine, 1, safeLine, model.getLineMaxColumn(safeLine)));
  editor.revealLineInCenterIfOutsideViewport(safeLine);
  editor.focus();
  cursorPosition();
}

function jumpToDiagnostic() {
  if (!currentError?.line) return;
  const { line, startColumn, endColumn } = inferredDiagnosticRange(currentError);
  editor.setSelection(new monaco.Range(line, startColumn, line, endColumn));
  editor.revealLineInCenterIfOutsideViewport(line);
  editor.focus();
  cursorPosition();
}

function jumpToTactic(step) {
  if (!step?.line) return;
  const model = editor.getModel();
  const line = Math.min(Math.max(1, step.line), model.getLineCount());
  const column = Math.min(Math.max(1, step.columnStart || 1), model.getLineMaxColumn(line));
  editor.setPosition({ lineNumber: line, column });
  editor.revealLineInCenterIfOutsideViewport(line);
  editor.focus();
  cursorPosition();
}

function fileTheoremIndices() {
  if (!result?.theorems || !activeFile()) return [];
  return result.theorems.flatMap((theorem, index) => resultFileBelongsHere(theorem.file) ? [index] : []);
}

function populateTheorems(preferred) {
  const indices = fileTheoremIndices();
  theoremSelect.innerHTML = indices.map(index => `<option value="${index}" title="${escapeHtml(result.theorems[index].name)}">${escapeHtml(shortTheoremName(result.theorems[index].name))}</option>`).join("");
  if (preferred !== undefined && indices.includes(preferred)) theoremSelect.value = String(preferred);
  else if (indices.length) theoremSelect.value = String(indices[0]);
}

function setProofHeading(title, statement = "") {
  theoremSelect.title = title;
  const summary = document.querySelector("#summary");
  summary.textContent = statement;
  summary.title = statement;
}

function selectProofPlaceholder(title) {
  theoremSelect.querySelector('option[value=""]')?.remove();
  const option = document.createElement("option");
  option.value = "";
  option.textContent = title;
  theoremSelect.prepend(option);
  theoremSelect.value = "";
}

function syncGoalToCursor(line = cursorLine(), column = cursorLocation().column) {
  if (!result || !activeFile()) return;
  const evaluation = result.evaluations?.find(item => resultFileBelongsHere(item.file) && item.line === line);
  if (evaluation) {
    const key = `${resultRevision}:${activeFile().id}:evaluation:${evaluation.line}`;
    if (key === lastCursorGoalKey) return;
    lastCursorGoalKey = key;
    theoremSelect.value = "";
    renderEvaluation(evaluation);
    return;
  }
  if (!result.theorems) return;
  const indices = fileTheoremIndices();
  const theoremIndex = indices.find(index => {
    const theorem = result.theorems[index];
    return line >= theorem.lineStart && line <= theorem.lineEnd;
  });
  if (theoremIndex === undefined) {
    const key = `${resultRevision}:${activeFile().id}:none`;
    if (key === lastCursorGoalKey) return;
    lastCursorGoalKey = key;
    theoremSelect.value = "";
    renderTheorem();
    return;
  }
  theoremSelect.value = String(theoremIndex);
  const theorem = result.theorems[theoremIndex];
  selectedStep = tacticStepAtCursor(visibleTheoremSteps(theorem), line, column);
  const key = `${resultRevision}:${activeFile().id}:theorem:${theoremIndex}:step:${selectedStep}`;
  if (key === lastCursorGoalKey) return;
  lastCursorGoalKey = key;
  renderTheorem();
}

function visibleTheoremSteps(theorem) {
  const file = files.find(item => fileResultNames(item).has(theorem.file));
  if (!file) return theorem.steps;
  const checkedSource = [...fileResultNames(file)].map(name => resultSources.get(name)).find(source => source !== undefined);
  return visibleTacticSteps(theorem.steps, checkedSource, file.source,
    Boolean(currentError && errorBelongsHere()));
}

function renderEvaluation(evaluation) {
  dismissGoalSymbolTooltip();
  selectProofPlaceholder("Evaluation");
  setProofHeading("Evaluation", `eval ${evaluation.expression}`);
  renderProofMap();
  renderInfo();
  document.querySelector("#goalView").innerHTML = `<div class="evaluation-caption">Evaluated at <code>line ${evaluation.line}</code></div><div class="evaluation-card"><code>${escapeHtml(evaluation.expression)}</code><span>⇒</span><strong>${escapeHtml(evaluation.value)}</strong></div>`;
  document.querySelector("#kernelSummary").textContent = "evaluation does not add a theorem";
  document.querySelector("#kernelView").innerHTML = "";
}

function selectedTheorem() {
  const theoremIndex = theoremSelect.value === "" ? undefined : Number(theoremSelect.value);
  return Number.isSafeInteger(theoremIndex) ? result?.theorems?.[theoremIndex] : undefined;
}

function renderTheorem() {
  dismissGoalSymbolTooltip();
  const theorem = selectedTheorem();
  if (!theorem) {
    const scope = result?.context === "bootstrap" ? "bootstrap stage checked" : "workspace checked";
    selectProofPlaceholder("No theorem at cursor");
    setProofHeading("No theorem at cursor", `${activeFile()?.name ?? "Workspace"} · ${scope}`);
    renderProofMap();
    renderInfo();
    document.querySelector("#goalView").innerHTML = '<div class="no-goals">Move the cursor into a theorem proof.</div>';
    document.querySelector("#kernelSummary").textContent = "";
    document.querySelector("#kernelView").innerHTML = "";
    return;
  }
  setProofHeading(shortTheoremName(theorem.name), theorem.statement);
  const visibleSteps = visibleTheoremSteps(theorem);
  const stages = [{ command: "initial", line: theorem.lineStart, before: theorem.initial, after: theorem.initial }, ...visibleSteps];
  selectedStep = Math.min(selectedStep, stages.length - 1);
  renderProofMap(theorem, cursorLine());
  const stage = stages[selectedStep];
  renderInfo(stage.info, stage);
  const traceErrorStage = Boolean(currentError?.trace) && selectedStep === stages.length - 1;
  const failedStage = traceErrorStage && stage.line === currentError.line;
  const staleError = currentError && !currentError.trace && errorBelongsHere()
    ? `<div class="proof-notice"><span>Working position: showing the last checked goal</span><small>${diagnosticMessageHtml(currentError.message)}</small></div>` : "";
  const stageCaption = selectedStep === 0 ? "Current goal, at theorem start"
    : failedStage ? `Current position, after line ${stage.line}`
    : `Current goal, after line ${stage.line}`;
  document.querySelector("#goalView").innerHTML = staleError + (selectedStep === 0
    ? renderState(stage.after, undefined, stageCaption, theorem)
    : `${traceErrorStage ? `<div class="proof-position"><span class="position-mark" aria-hidden="true">◆</span><div class="position-copy"><code>${failedStage ? `line ${stage.line}` : "in progress"}</code><span>${diagnosticMessageHtml(currentError.message)}</span></div></div>` : ""}${renderState(stage.after, stage.before, stageCaption, theorem)}`);
  const complete = !stage.after?.goals?.length;
  const sorryCount = theorem.sorries?.length ?? 0;
  document.querySelector("#kernelSummary").textContent = theorem.kernel.length ? `${theorem.kernel.length} proof lines`
    : complete ? (sorryCount ? `${sorryCount} ${sorryCount === 1 ? "sorry" : "sorries"}` : "goals = ∅") : "available after completion";
  if (document.querySelector("#kernelDrawer").open) {
    // An already open drawer (a derivation link, or a drawer left open across
    // a re-check) fetches the kernel details it does not yet have.
    if (theorem.kernel.length || !complete || sorryCount || kernelLoading.has(theorem.name)) renderKernel(theorem);
    else { kernelLoading.add(theorem.name); void renderSelectedKernel().finally(() => kernelLoading.delete(theorem.name)); }
  } else document.querySelector("#kernelView").innerHTML = "";
}
const kernelLoading = new Set();
let maximizeKernelOnRender = false;

async function renderSelectedKernel() {
  const theoremIndex = theoremSelect.value === "" ? undefined : Number(theoremSelect.value);
  const theorem = theoremIndex !== undefined && Number.isSafeInteger(theoremIndex) ? result?.theorems?.[theoremIndex] : undefined;
  if (!theorem) return;
  if (theorem.kernel.length) return renderKernel(theorem);
  const generation = checkGeneration;
  const theoremName = theorem.name;
  document.querySelector("#kernelSummary").textContent = "loading checked kernel proof…";
  try {
    const inspected = await requestWorkbench("inspect", {
      files: workspacePayload(), activeFile: activeFile().name,
    });
    if (generation !== checkGeneration || !inspected.ok) return;
    const details = inspected.theorems.find(item => item.name === theoremName);
    if (!details) return;
    Object.assign(theorem, {
      proofNodes: details.proofNodes,
      judgments: details.judgments,
      dependencies: details.dependencies,
      kernel: details.kernel,
    });
    document.querySelector("#kernelSummary").textContent = `${theorem.kernel.length} proof lines`;
    if (document.querySelector("#kernelDrawer").open) renderKernel(theorem);
    // A derivation link gives the proof the whole pane.
    if (maximizeKernelOnRender) { maximizeKernelOnRender = false; setKernelDrawerHeight(Number.MAX_SAFE_INTEGER); }
  } catch (error) {
    document.querySelector("#kernelSummary").textContent = error.message || "kernel proof unavailable";
  }
}

function renderKernel(theorem) {
  const ordered = kernelFitchOrder(theorem.kernel);
  const byId = new Map(theorem.kernel.map(node => [node.id, node]));
  const contextKey = node => JSON.stringify(node.assumptions);
  const referenceById = new Map(ordered.map((node, index) => {
    let start = index;
    while (start > 0 && contextKey(ordered[start - 1]) === contextKey(node)) start -= 1;
    const reference = start < index && node.assumptions.length > 0 ? `${ordered[start].fitchLine}–${node.fitchLine}` : String(node.fitchLine);
    return [node.id, reference];
  }));
  const cited = new Set(theorem.kernel.flatMap(node => node.children));
  const root = theorem.kernel.find(node => !cited.has(node.id));
  const baseDepth = root?.assumptions?.length ?? 0;
  const lines = ordered.map((node, index) => {
    const depth = Math.max(0, node.assumptions.length - baseDepth);
    const scopeStart = depth > 0 && (index === 0 || contextKey(ordered[index - 1]) !== contextKey(node));
    const rails = Array.from({ length: depth }, () => '<i class="fitch-rail"></i>').join("");
    const citations = node.children.map((id, index) => {
      const line = referenceById.get(id);
      const role = node.premiseLabels?.[index] || `premise ${index + 1}`;
      return `<a href="#kernel-line-${id}" title="${escapeHtml(role)}">${line ?? "?"}</a>`;
    }).join(", ");
    const rule = escapeHtml(node.ruleCode || node.rule);
    const justification = citations ? `${rule} ${citations}` : rule;
    const args = node.arguments?.length ? `<dl class="fitch-arguments">${node.arguments.map(argument =>
      `<div><dt>${escapeHtml(argument.name)}</dt><dd>${escapeHtml(argument.value)}</dd></div>`).join("")}</dl>` : "";
    const premises = node.children.length ? node.children.map((id, premiseIndex) => {
      const premise = byId.get(id);
      const inherited = node.assumptions.every((assumption, assumptionIndex) => premise?.assumptions?.[assumptionIndex] === assumption);
      const discharged = inherited ? premise.assumptions.slice(node.assumptions.length) : [];
      const reference = referenceById.get(id) ?? "?";
      const role = node.premiseLabels?.[premiseIndex] || `premise ${premiseIndex + 1}`;
      const assumptions = discharged.length ? `<div class="nd-discharged">${discharged.map(assumption => `<code>[${escapeHtml(assumption)}]</code>`).join("")}</div>` : "";
      return `<div class="nd-premise">${assumptions}<code>${escapeHtml(premise?.conclusion || "premise")}</code><span>${escapeHtml(role)} · <a href="#kernel-line-${id}">${reference.includes("–") ? "lines" : "line"} ${reference}</a></span></div>`;
    }).join("") : "";
    const sideConditions = node.sideConditions?.length ? `<div class="nd-side-conditions"><span>${node.sideConditions.length === 1 ? "Side condition" : "Side conditions"}</span>${node.sideConditions.map(condition => `<code>${escapeHtml(condition)}</code>`).join("")}</div>` : "";
    const inference = `<div class="nd-inference"><div class="nd-rule"><div class="nd-premises">${premises}</div><div class="nd-rule-bar"><span></span><strong>${rule}</strong></div><code class="nd-conclusion">${escapeHtml(node.conclusion)}</code></div><aside class="nd-rule-aside"><strong>${escapeHtml(node.ruleName || node.rule)}</strong>${sideConditions}</aside></div>`;
    return `<details class="fitch-line ${scopeStart ? "scope-start" : ""} ${node.rule === "assumption" ? "assumption" : ""}" id="kernel-line-${node.id}"><summary><span class="fitch-number">${node.fitchLine}</span><span class="fitch-formula"><span class="fitch-rails" aria-hidden="true">${rails}</span><code>${escapeHtml(node.conclusion)}</code></span><span class="fitch-justification"><strong>${justification}</strong><small>${escapeHtml(node.ruleName || node.rule)}</small></span></summary><div class="fitch-detail" style="--fitch-depth:${depth}">${inference}${args}</div></details>`;
  }).join("");
  document.querySelector("#kernelView").innerHTML = `<div class="fitch-guide">Premises precede conclusions. Select a line for its natural-deduction rule and exact kernel arguments.</div><div class="fitch-proof">${lines}</div>`;
}

function renderProofMap(theorem, line = 0) {
  const drawer = document.querySelector("#proofMapDrawer");
  const map = document.querySelector("#proofMap");
  const summary = document.querySelector("#proofMapSummary");
  const entries = theorem?.proofMap || [];
  if (!entries.length) {
    drawer.hidden = true;
    map.innerHTML = "";
    summary.textContent = "";
    return;
  }
  const visibleSteps = visibleTheoremSteps(theorem);
  const tree = proofMapSections(entries, visibleSteps);
  const headings = entries.filter(entry => entry.kind === "heading");
  const currentStep = selectedStep > 0 ? visibleSteps[selectedStep - 1] : undefined;
  const activeLine = currentStep?.line ?? line;
  const containing = headings.filter((heading, index) => {
    const end = headings.slice(index + 1).find(next => next.indent <= heading.indent)?.line ?? Infinity;
    return heading.line <= activeLine && activeLine < end;
  });
  const active = containing.sort((left, right) => right.indent - left.indent || right.line - left.line)[0]?.line;
  const activePath = new Set(containing.map(entry => entry.line));
  summary.textContent = `${headings.length} ${headings.length === 1 ? "landmark" : "landmarks"}`;
  const sectionHtml = section => {
    const key = `${theorem.name}:${section.line}`;
    const open = activePath.has(section.line) || expandedProofSections.has(key);
    const tacticCount = section.steps.length + section.sections.reduce((sum, child) => sum + countSectionTactics(child), 0);
    return `<details class="proof-map-section ${section.line === active ? "active" : ""}" data-section="${escapeHtml(key)}" ${open ? "open" : ""}><summary><strong>${escapeHtml(section.text)}</strong><span>${tacticCount} ${tacticCount === 1 ? "tactic" : "tactics"}</span><button class="proof-map-jump" type="button" data-line="${section.line}" title="Go to explanation">line ${section.line}</button></summary><div class="proof-map-body">${section.notes.map(note => `<div class="proof-map-note">${escapeHtml(note.text)}</div>`).join("")}${section.steps.map((step, index) => tacticHtml(step, visibleSteps.indexOf(step), index)).join("")}${section.sections.map(sectionHtml).join("")}</div></details>`;
  };
  map.innerHTML = `${tree.notes.map(note => `<div class="proof-map-note root">${escapeHtml(note.text)}</div>`).join("")}${tree.steps.map((step, index) => tacticHtml(step, visibleSteps.indexOf(step), index)).join("")}${tree.sections.map(sectionHtml).join("")}`;
  map.querySelectorAll(".proof-map-section").forEach(section => section.addEventListener("toggle", () => {
    if (section.open) expandedProofSections.add(section.dataset.section);
    else expandedProofSections.delete(section.dataset.section);
  }));
  map.querySelectorAll(".proof-map-jump").forEach(button => button.addEventListener("click", event => {
    event.preventDefault();
    event.stopPropagation();
    jumpToLine(Number(button.dataset.line));
  }));
  map.querySelectorAll(".proof-map-tactic").forEach(button => button.addEventListener("click", () => jumpToTactic(visibleSteps[Number(button.dataset.step)])));
  drawer.hidden = false;
}

function countSectionTactics(section) {
  return section.steps.length + section.sections.reduce((sum, child) => sum + countSectionTactics(child), 0);
}

function tacticHtml(step, stepIndex) {
  const goals = step.after?.goals?.length ?? 0;
  const resultLabel = goals === 0 ? "complete" : `${goals} ${goals === 1 ? "goal" : "goals"}`;
  const active = stepIndex + 1 === selectedStep;
  return `<button class="proof-map-tactic ${active ? "active" : ""}" type="button" data-step="${stepIndex}"><code>${escapeHtml(step.command)}</code><span>${escapeHtml(resultLabel)}</span></button>`;
}

function sorryDashArray(count) {
  const gaps = Math.min(4, Math.max(1, count));
  const gap = 8;
  const dash = (100 - gap * gaps) / (gaps + 1);
  return `${dash.toFixed(4)} ${gap}`;
}

function qedMark(state, count = 0) {
  const sorry = state === "sorry";
  const barDash = sorry ? ` stroke-dasharray="${sorryDashArray(count)}"` : "";
  return `<svg class="qed-mark ${state}" viewBox="0 0 240 120" role="img" aria-label="${sorry ? "Proof complete modulo sorries" : "Proof complete"}"><path class="qed-letter qed-q" transform="translate(22 88) scale(.1 -.1)" d="M413 -180V144H412Q402 93 363.5 65Q325 37 267 37Q182 37 133 91.5Q84 146 84 241V354Q84 449 133 504.5Q182 560 267 560Q327 560 365.5 532Q404 504 414 453H415V550H511V-180ZM298 120Q351 120 382 153Q413 186 413 246V349Q413 408 382 441Q351 474 298 474Q243 474 213 442.5Q183 411 183 357V237Q183 183 213 151.5Q243 120 298 120Z"/><g class="qed-membership" transform="translate(-108.24 -17.94) scale(.78)"><path class="qed-e-arc" pathLength="100" d="M 310 77.92 A 28 28 0 1 0 310 121.92"/><path class="qed-e-bar" pathLength="100" d="M 269.09 99.92 L 311.92 99.92"${barDash}/></g><path class="qed-letter qed-d" transform="translate(158 88) scale(.1 -.1)" d="M267 -10Q182 -10 133 44.5Q84 99 84 194V307Q84 402 133 457.5Q182 513 267 513Q325 513 363.5 485Q402 457 413 408H414V730H511V0H414V95H413Q403 44 364.5 17Q326 -10 267 -10ZM298 77Q351 77 382 110Q413 143 413 203V306Q413 365 382 398Q351 431 298 431Q243 431 213 399.5Q183 368 183 314V194Q183 140 213 108.5Q243 77 298 77Z"/></svg>`;
}

function completionAnimation(theorem) {
  if (!theorem || playedQedAnimations.has(theorem.name)) return { className: "", style: "" };
  playedQedAnimations.add(theorem.name);
  const transition = qedTransitions.get(theorem.name);
  if (transition?.kind === "upgrade") return {
    className: "qed-upgrade",
    style: ` style="--qed-upgrade-dash: ${sorryDashArray(transition.previous)}"`,
  };
  return { className: "qed-new", style: "" };
}

function renderState(state, previous, caption = "Current goal", theorem) {
  const sorries = theorem?.sorries || [];
  const file = activeFile();
  const checkedSource = file && [...fileResultNames(file)].map(name => resultSources.get(name)).find(source => source !== undefined);
  const auditAction = renderAxiomAuditAction(state, theorem, Boolean(file && checkedSource === file.source && !currentError));
  if (!state?.goals?.length && sorries.length) {
    const count = sorries.length;
    const expanded = expandedSorryTheorems.has(theorem.name);
    const sites = expanded ? `<ol class="sorry-sites" aria-label="Sorry sites">${sorries.map((site, index) => {
      const documentName = result?.documents?.find(document => document.file === site.file)?.name || site.file;
      return `<li><button type="button" data-sorry-site="${index}"><code>${escapeHtml(documentName)}:${site.line}</code><span><strong>${escapeHtml(shortTheoremName(site.theorem))}</strong><small>${escapeHtml(site.goal)}</small></span><i aria-hidden="true">open ▸</i></button></li>`;
    }).join("")}</ol>` : "";
    return `<div class="qed-state qed-sorry ${expanded ? "expanded" : ""}">${qedMark("sorry", count)}<span class="qed-copy">Proof complete, modulo ${count} ${count === 1 ? "sorry" : "sorries"}</span><span class="qed-actions">${auditAction}<button type="button" class="qed-show" data-toggle-sorries aria-expanded="${expanded}">${expanded ? "hide" : "show"} <span aria-hidden="true">${expanded ? "▾" : "▸"}</span></button></span>${sites}</div>`;
  }
  if (!state?.goals?.length) {
    const animation = completionAnimation(theorem);
    return `<div class="qed-state qed-proven ${animation.className}"${animation.style}>${qedMark("proven")}<span class="qed-copy">No goals remain: proof complete</span>${auditAction}</div>`;
  }
  return state.goals.map((goal, index) => {
    const prior = previous?.goals?.[index];
    const semanticSymbols = [...goal.locals, ...goal.assumptions.map(formula => ({ formula }))];
    // The sorts of variables, `k : ℕ`, are routine: they are gathered into
    // one line, grouped by sort, rather than listed as hypotheses.
    const variableSort = /^([\p{L}_][\p{L}\p{M}\p{N}_]*) : ([ℕℤℚℝ])$/u;
    const sorts = new Map();
    const noteSort = formula => {
      const match = variableSort.exec(formula);
      if (!match) return false;
      if (!sorts.has(match[2])) sorts.set(match[2], []);
      if (!sorts.get(match[2]).includes(match[1])) sorts.get(match[2]).push(match[1]);
      return true;
    };
    const locals = goal.locals.filter(local => !noteSort(local.formula)).map(local => {
      const old = prior?.locals?.find(item => item.name === local.name)?.formula;
      return `<div class="${old === undefined ? "goal-change-line" : ""}"><span class="local-name">${escapeHtml(local.name)}</span> : ${changedText(local.formula, old, goal.locals)}</div>`;
    }).join("");
    const assumptions = goal.assumptions.filter(item => !goal.locals.some(local => local.formula === item) && !noteSort(item));
    const sortsHtml = sorts.size
      ? `<div class="context-sorts">${[...sorts].map(([sort, names]) => `${names.map(escapeHtml).join(" ")} : ${sort}`).join(", ")}</div>` : "";
    const assumptionsHtml = sortsHtml + assumptions.map(item => `<div class="${prior && !prior.assumptions.includes(item) ? "goal-change-line" : ""}">· ${renderSemanticText(item, semanticSymbols)}</div>`).join("");
    return `<div class="goal-card"><div class="goal-meta"><span>${escapeHtml(caption)}</span><code>${index + 1} of ${state.goals.length}</code></div><div class="context">${locals}${assumptionsHtml || (goal.locals.length ? "" : "<div class=\"empty-context\">No assumptions</div>")}</div><div class="turnstile">${changedText(goal.goal, prior?.goal, semanticSymbols)}</div></div>`;
  }).join("");
}

function changedText(value, previous, localSymbols = []) {
  const parts = changedTextParts(value, previous);
  if (!parts.changed) return renderSemanticText(value, localSymbols);
  return `${renderSemanticText(parts.prefix, localSymbols)}<span class="goal-change">${renderSemanticText(parts.changed, localSymbols)}</span>${renderSemanticText(parts.suffix, localSymbols)}`;
}

function renderSemanticText(value, localSymbols = []) {
  const text = String(value);
  const parameters = declaredParameterNames(source.value, source.selectionStart || 0);
  let html = "";
  let index = 0;
  const notationTokens = [...new Set((result?.notations || []).map(notation => notation.token).filter(Boolean))]
    .sort((left, right) => right.length - left.length);
  while (index < text.length) {
    const exactToken = tokenAtTextOffset(text, index);
    const exactSymbol = exactToken?.start === index ? resolveNamedSymbol(exactToken.text) : undefined;
    const subscriptNotation = exactSymbol ? undefined : subscriptNotationAtTextOffset(text, index, parameters);
    if (subscriptNotation) {
      const symbol = resolveNamedSymbol(subscriptNotation.target);
      html += symbol
        ? semanticSymbolHtml(subscriptNotation.text, symbol, subscriptNotation.literal,
          `${subscriptNotation.literal} elaborates to ${subscriptNotation.desugaring}\n${symbol.info}`)
        : escapeHtml(subscriptNotation.text);
      index += subscriptNotation.text.length;
      continue;
    }
    const equivalenceNotation = equivalenceClassNotationAtTextOffset(text, index);
    if (equivalenceNotation) {
      const symbol = resolveNamedSymbol(equivalenceNotation.target);
      html += symbol
        ? semanticSymbolHtml(equivalenceNotation.text, symbol, equivalenceNotation.literal,
          `${equivalenceNotation.literal} elaborates to ${equivalenceNotation.desugaring}\n${symbol.info}`)
        : escapeHtml(equivalenceNotation.text);
      index += equivalenceNotation.text.length;
      continue;
    }
    const orderedPairNotation = orderedPairNotationAtTextOffset(text, index);
    if (orderedPairNotation) {
      const symbol = resolveNamedSymbol(orderedPairNotation.target);
      html += symbol
        ? semanticSymbolHtml(orderedPairNotation.text, symbol, orderedPairNotation.literal,
          `${orderedPairNotation.literal} elaborates to ${orderedPairNotation.desugaring}\n${symbol.info}`)
        : escapeHtml(orderedPairNotation.text);
      index += orderedPairNotation.text.length;
      continue;
    }
    const setNotation = setNotationAtTextOffset(text, index);
    if (setNotation) {
      const symbol = resolveSetNotationSymbol(setNotation.target);
      html += symbol
        ? semanticSymbolHtml(setNotation.text, symbol, setNotation.literal, `${setNotation.literal} elaborates to ${setNotation.desugaring}\n${symbol.info}`)
        : escapeHtml(setNotation.text);
      index += setNotation.text.length;
      continue;
    }
    const notation = notationTokens.find(token => text.startsWith(token, index));
    if (notation) {
      const symbol = notationSymbol({ text: notation, start: index, end: index + notation.length }, { text, localSymbols });
      // The tooltip shows the notation's own account (display, elaboration,
      // supplying hypothesis), not the bare underlying symbol's.
      html += symbol ? semanticSymbolHtml(notation, { ...symbol, local: true }, notation, symbol.info) : escapeHtml(notation);
      index += notation.length;
      continue;
    }
    const identifier = /^[\p{L}\p{M}_ℕ][\p{L}\p{M}\p{N}_.'?-]*/u.exec(text.slice(index));
    if (identifier) {
      const local = localSymbols.find(item => item.name === identifier[0]);
      const isCall = /^\s*\(/.test(text.slice(index + identifier[0].length));
      const symbol = local ? { name: local.name, short: local.name, kind: "local", info: `${local.name} : ${local.formula}`, local: true }
        : resolveNamedSymbol(identifier[0], { call: isCall });
      html += symbol ? semanticSymbolHtml(identifier[0], symbol, undefined, symbol.local ? symbol.info : undefined) : escapeHtml(identifier[0]);
      index += identifier[0].length;
      continue;
    }
    html += escapeHtml(text[index++]);
  }
  return html;
}

function semanticSymbolHtml(label, symbol, notation, semanticInfo) {
  const notationAttribute = notation ? ` data-notation="${escapeHtml(notation)}"` +
    (symbol.written ? ` data-written="${escapeHtml(symbol.written)}" data-elaborated="${escapeHtml(symbol.elaborated || "")}"` : "") +
    (symbol.declaration ? ` data-declaration="${escapeHtml(symbol.declaration)}"` : "") +
    (symbol.module ? ` data-module="${escapeHtml(symbol.module)}"` : "") : "";
  const infoAttribute = semanticInfo ? ` data-semantic-info="${escapeHtml(semanticInfo)}"` : "";
  const localAttributes = symbol.local || symbol.ephemeral ? ` data-local-symbol="true" data-symbol-short="${escapeHtml(symbol.short)}" data-symbol-kind="${escapeHtml(symbol.kind)}"` : "";
  const navigation = symbol.line ? ' role="link" tabindex="0"' : ' tabindex="0"';
  return `<span class="semantic-symbol ${symbol.line ? "navigable" : ""}" data-symbol-name="${escapeHtml(symbol.name)}"${notationAttribute}${infoAttribute}${localAttributes}${navigation}>${escapeHtml(label)}</span>`;
}

function positionGoalTooltip(clientX, clientY) {
  const margin = 12;
  const left = Math.min(clientX + margin, innerWidth - goalSymbolTooltip.offsetWidth - margin);
  const top = Math.min(clientY + margin, innerHeight - goalSymbolTooltip.offsetHeight - margin);
  goalSymbolTooltip.style.left = `${Math.max(margin, left)}px`;
  goalSymbolTooltip.style.top = `${Math.max(margin, top)}px`;
}

function renderInfo(info, stage) {
  const drawer = document.querySelector("#infoDrawer");
  const view = document.querySelector("#infoView");
  const summary = document.querySelector("#infoSummary");
  if (!info?.items?.length) {
    view.innerHTML = '<div class="info-empty">Use <code>exact?</code>, <code>apply?</code>, or <code>rw?</code> to search the checked environment.</div>';
    summary.textContent = "Proof search";
    return;
  }
  summary.textContent = `${info.items.length} ${info.items.length === 1 ? "suggestion" : "suggestions"}`;
  view.innerHTML = `<div class="info-title">${escapeHtml(info.title)}</div>${info.items.map((item, index) => `<button class="suggestion" data-suggestion="${index}"><code>${escapeHtml(item)}</code><span>${index === 0 ? "used" : "available"}</span></button>`).join("")}`;
  view.querySelectorAll(".suggestion").forEach(button => button.addEventListener("click", () => {
    const replacement = info.items[Number(button.dataset.suggestion)];
    if (!replacement || !stage?.line) return;
    const lines = source.value.split("\n");
    const lineStart = lines.slice(0, stage.line - 1).reduce((sum, line) => sum + line.length + 1, 0);
    const start = lineStart + Math.max(0, (stage.columnStart || 1) - 1);
    const end = lineStart + Math.max(start - lineStart, (stage.columnEnd || lines[stage.line - 1]?.length + 1) - 1);
    source.setRangeText(replacement, start, end, "end");
    source.dispatchEvent(new Event("input"));
    source.focus();
  }));
  drawer.open = true;
}

function shortTheoremName(name) {
  const candidates = result?.symbols?.filter(symbol => symbol.kind === "theorem" && symbol.name === name);
  return candidates?.[0]?.short || name.split(".").at(-1);
}

function tokenAt(offset) {
  return tokenAtTextOffset(source.value, offset);
}

function symbolAtOffset(offset) {
  const imported = importSymbolAt(source.value, offset, files, bundledModuleIndex, result?.documents);
  if (imported) return imported;
  const declaration = declarationHelpAtTextOffset(source.value, offset);
  if (declaration) return {
    name: declaration.form, short: declaration.text, kind: "declaration form",
    info: `${declaration.entry.syntax}\n${declaration.entry.summary}\n${declaration.entry.detail}\n\nExample:\n${declaration.entry.example}`,
    token: declaration,
  };
  if (source.value[offset] === "∫") {
    const symbol = resolveNamedSymbol("riemannIntegral");
    if (symbol) return {
      ...symbol, short: "∫[A, B] f", kind: `notation for ${symbol.kind}`,
      info: `∫[A, B] f elaborates to riemannIntegral(f, A, B)\n${symbol.info}`,
      notationTarget: symbol.name, token: { text: "∫", start: offset, end: offset + 1 },
    };
  }
  const exactToken = tokenAtTextOffset(source.value, offset);
  const subscriptNotation = exactToken && resolveNamedSymbol(exactToken.text)
    ? undefined : subscriptNotationAtTextOffset(source.value, offset);
  if (subscriptNotation) {
    const symbol = resolveNamedSymbol(subscriptNotation.target);
    if (symbol) return {
      ...symbol, short: subscriptNotation.literal, kind: `notation for ${symbol.kind}`,
      info: `${subscriptNotation.literal} elaborates to ${subscriptNotation.desugaring}\n${symbol.info}`,
      notationTarget: symbol.name, token: subscriptNotation,
    };
  }
  const equivalenceNotation = equivalenceClassNotationAtTextOffset(source.value, offset);
  if (equivalenceNotation) {
    const symbol = resolveNamedSymbol(equivalenceNotation.target);
    if (symbol) return {
      ...symbol, short: equivalenceNotation.literal, kind: `notation for ${symbol.kind}`,
      info: `${equivalenceNotation.literal} elaborates to ${equivalenceNotation.desugaring}\n${symbol.info}`,
      notationTarget: symbol.name, token: equivalenceNotation,
    };
  }
  const orderedPairNotation = orderedPairNotationAtTextOffset(source.value, offset);
  if (orderedPairNotation) {
    const symbol = resolveNamedSymbol(orderedPairNotation.target);
    if (symbol) return {
      ...symbol, short: orderedPairNotation.literal, kind: `notation for ${symbol.kind}`,
      info: `${orderedPairNotation.literal} elaborates to ${orderedPairNotation.desugaring}\n${symbol.info}`,
      notationTarget: symbol.name, token: orderedPairNotation,
    };
  }
  const setNotation = setNotationAtTextOffset(source.value, offset);
  if (setNotation) {
    const symbol = resolveSetNotationSymbol(setNotation.target);
    if (symbol) return {
      ...symbol,
      short: setNotation.literal,
      kind: `notation for ${symbol.kind}`,
      info: `${setNotation.literal} elaborates to ${setNotation.desugaring}\n${symbol.info}`,
      notationTarget: symbol.name,
      token: setNotation,
    };
  }
  const activeResult = resultFileBelongsHere(resultActiveFile) ? result : undefined;
  const notationToken = notationAtTextOffset(source.value, offset, activeResult?.notations);
  if (notationToken) return notationSymbol(notationToken);
  const tacticNames = [...new Set([
    ...documentedTacticFamilies,
    ...(activeResult?.tactics || []).map(tactic => tactic.short),
  ])];
  const tacticToken = tacticTokenAtTextOffset(source.value, offset, tacticNames);
  if (tacticToken) return tacticSymbol(tacticToken);
  const token = tokenAt(offset);
  if (!token || !activeResult?.symbols) return undefined;
  // A name the surrounding section, header, or proof binds shadows every
  // declaration of that name: `with ideal` means the hypothesis, not a
  // theorem whose short name is `ideal`.
  const fromTrace = boundNameFromResult(token, offset);
  if (fromTrace) return fromTrace;
  const bound = localNamesAtOffset(source.value, offset).get(token.text);
  if (bound) {
    const traced = localSymbol(token);
    return traced ? { ...traced, kind: bound.kind } : { name: token.text, short: token.text, kind: bound.kind, info: bound.info, token };
  }
  const symbol = resolveNamedSymbol(token.text, { call: /^\s*\(/.test(source.value.slice(token.end)) });
  return symbol ? { ...symbol, token } : localSymbol(token);
}

/**
 * The binding of a name at `offset` from the checked result: the theorem
 * whose lines contain the offset carries the names its sections and header
 * bind (`scope`), and the step states carry the locals the proof binds, so
 * the name is looked up in the state before the step on the hovered line.
 * Undefined when no checked theorem covers the line, which leaves the text
 * scan of `localNamesAtOffset` as the fallback.
 */
function boundNameFromResult(token, offset) {
  if (!result?.theorems || !resultFileBelongsHere(resultActiveFile)) return undefined;
  const line = source.value.slice(0, offset).split("\n").length;
  const index = fileTheoremIndices().find(item => line >= result.theorems[item].lineStart && line <= result.theorems[item].lineEnd);
  if (index === undefined) return undefined;
  const theorem = result.theorems[index];
  const entry = theorem.scope?.find(item => item.name === token.text);
  if (theorem.initial) {
    const stages = [{ line: theorem.lineStart, after: theorem.initial }, ...visibleTheoremSteps(theorem)];
    const next = stages.findIndex((stage, position) => position > 0 && stage.line >= line);
    const current = next < 0 ? stages[stages.length - 1] : stages[next - 1];
    const locals = current.after?.goals?.flatMap(goal => goal.locals) || [];
    const local = locals.find(item => item.name === token.text);
    if (local) {
      const bound = entry ? entry.line : stages.find(stage => stage.after?.goals?.some(goal => goal.locals.some(item => item.name === token.text)))?.line;
      return {
        name: token.text, short: token.text, kind: entry?.kind || "local proof",
        info: `${token.text} : ${local.formula}`, file: theorem.file, line: bound, token,
      };
    }
  }
  if (!entry) return undefined;
  return {
    name: token.text, short: token.text, kind: entry.kind,
    info: entry.sort ? `${token.text} : ${entry.sort}` : `${token.text}, bound on line ${entry.line}`,
    file: theorem.file, line: entry.line, token,
  };
}

/** The names bound by binder groups `(a b : T)`, `{A : Set}`, or `(x ∈ A)`. */
function binderGroupNames(text) {
  const names = [];
  for (const group of text.matchAll(/[({]([^(){}]*)[)}]/gu)) {
    const inner = group[1];
    const separator = inner.search(/[:∈⊆]/u);
    if (separator < 0) continue;
    names.push(...inner.slice(0, separator).trim().split(/\s+/u).filter(Boolean));
  }
  return names;
}

/**
 * The names a proof line at `offset` can refer to without naming a
 * declaration: hypotheses and variables of the open sections, the
 * enclosing header's premises and binders, and the proof's own locals
 * on the lines above. Each maps to its kind and a one-line description.
 */
function localNamesAtOffset(text, offset) {
  const names = new Map();
  const lines = text.slice(0, offset).split("\n");
  const sections = [[]];
  const headerNames = [];
  const bind = (name, kind, info, scope) => {
    if (!name) return;
    names.set(name, { kind, info });
    scope.push(name);
  };
  const unbindAll = scope => { for (const name of scope.splice(0)) names.delete(name); };
  const lastLine = lines.length - 1;
  for (let i = 0; i < lastLine; i++) {
    const line = lines[i];
    let match;
    if (/^section\b/u.test(line)) sections.push([]);
    else if (/^end\b/u.test(line)) { if (sections.length > 1) unbindAll(sections.pop()); }
    else if ((match = /^hypothesis\s+([^\s:]+)\s*:\s*(.*)$/u.exec(line))) {
      bind(match[1], "section hypothesis", `${match[1]} : ${match[2]}`, sections.at(-1));
    } else if ((match = /^variable\s+(.*)$/u.exec(line))) {
      for (const name of binderGroupNames(match[1])) bind(name, "section variable", `${name} : variable of the section`, sections.at(-1));
    } else if ((match = /^(theorem|lemma|instance|def\w*|predicate|class|structure|datatype|eval|notation)\b\s*(.*)$/u.exec(line))) {
      unbindAll(headerNames);
      for (const name of binderGroupNames(match[2])) bind(name, "binder", `${name} : binder of the header`, headerNames);
    } else if ((match = /^\s+requires\s+([^\s:]+)\s*:\s*(.*)$/u.exec(line))) {
      bind(match[1], "premise", `${match[1]} : ${match[2]}`, headerNames);
    } else if ((match = /^\s+have\s+([^\s:(]+)/u.exec(line))) {
      bind(match[1], "local proof", `${match[1]} : local proof of this theorem`, headerNames);
    } else if ((match = /^\s+obtain\s+⟨([^⟩]*)⟩/u.exec(line))) {
      for (const name of match[1].split(/[\s,]+/u).filter(Boolean)) bind(name, "local", `${name} : obtained on line ${i + 1}`, headerNames);
    } else if ((match = /^\s+intros?\s+(.*)$/u.exec(line))) {
      for (const name of match[1].replace(/\s+at\s+.*$/u, "").split(/[\s,]+/u).filter(Boolean)) {
        bind(name, "local", `${name} : introduced on line ${i + 1}`, headerNames);
      }
    } else if ((match = /^\s+r?cases\b.*\bwith\s+(.*)$/u.exec(line))) {
      for (const name of match[1].split(/[\s|⟨⟩,]+/u).filter(Boolean)) bind(name, "local", `${name} : case on line ${i + 1}`, headerNames);
    }
  }
  return names;
}

function tacticSymbol(token) {
  const macro = (resultFileBelongsHere(resultActiveFile) ? result?.tactics || [] : [])
    .find(item => item.short === token.text || item.name === token.text);
  if (macro) return {
    name: macro.name,
    short: token.text,
    kind: "tactic macro",
    info: `${macro.short}${macro.parameters.length ? `(${macro.parameters.join(", ")})` : ""} := ${macro.body}`,
    file: macro.file,
    line: macro.line,
    token,
  };
  const entries = tacticHelpEntries(token.text);
  if (!entries.length) return undefined;
  return {
    name: token.text,
    short: token.text,
    kind: "built-in tactic",
    info: entries.map(entry => `${entry.syntax}\n${entry.summary}\n${entry.detail}`).join("\n\n"),
    token,
  };
}

function resolveSetNotationSymbol(target) {
  if (target === "singleton") {
    return result?.symbols?.find(symbol => symbol.name === "Grace.Cumulus.Set.Basic.Set.singleton")
      || resolveNamedSymbol(target);
  }
  return resolveNamedSymbol(target);
}

function resolveNamedSymbol(name, options = {}) {
  if (!resultFileBelongsHere(resultActiveFile) || !result?.symbols) return undefined;
  const activeSourceFile = activeFile()?.sourceFile || activeFile()?.name;
  if (symbolCacheResult !== result) {
    symbolCacheResult = result;
    symbolResolutionCache.clear();
  }
  const context = {
    ...options,
    module: moduleName(activeFile()?.source || "", activeFile()?.sourceFile || activeFile()?.name || ""),
    file: activeSourceFile,
    theorem: selectedTheorem()?.name,
  };
  const key = `${name}\n${context.call ? "call" : "value"}\n${context.module || ""}\n${context.file || ""}\n${context.theorem || ""}`;
  if (symbolResolutionCache.has(key)) return symbolResolutionCache.get(key);
  const symbol = resolveSymbolCandidate(result.symbols, name, context);
  symbolResolutionCache.set(key, symbol);
  return symbol;
}

function notationSymbol(token, context) {
  const candidates = [...(result?.notations || [])].filter(item => item.token === token.text);
  const supplied = hypothesisNotationSymbol(token, candidates.filter(item => item.hypothesis), context);
  if (supplied) return supplied;
  let notation;
  if (candidates.length > 1) {
    const previous = source.value.slice(0, token.start).search(/\S\s*$/);
    const nextRelative = source.value.slice(token.end).search(/\S/);
    const leftToken = previous >= 0 ? tokenAtTextOffset(source.value, previous) : undefined;
    const rightToken = nextRelative >= 0 ? tokenAtTextOffset(source.value, token.end + nextRelative) : undefined;
    const leftType = leftToken ? (/^\d+$/u.test(leftToken.text) ? "Nat" : localTypeAt(leftToken)) : undefined;
    const rightType = rightToken ? (/^\d+$/u.test(rightToken.text) ? "Nat" : localTypeAt(rightToken)) : undefined;
    notation = notationForOperandTypes(candidates, leftType, rightType);
    const contextualType = context ? notationOperandTypeAtTextOffset(
      context.text, token, context.localSymbols, result?.notations || [],
    ) : undefined;
    const operandType = contextualType || (leftType && leftType === rightType ? leftType : undefined);
    notation ||= operandType ? [...candidates].reverse().find(item => item.operandType?.split(".").at(-1) === operandType) : undefined;
    if (!notation) return {
      name: token.text,
      short: token.text,
      kind: "overloaded notation",
      info: candidates.map(item => `${notationTypeLabel(item)}: ${token.text} → ${item.target}`).join("\n"),
      ephemeral: true,
      token,
    };
  } else notation = candidates[0];
  if (!notation) return undefined;
  const selected = notation.leadingArguments?.[0];
  const selectedName = selected?.tag === "app" && selected.args?.length === 0 ? selected.fn : undefined;
  const underlyingName = selectedName || notation.target;
  const underlying = result?.symbols?.find(symbol => symbol.name === underlyingName);
  if (!underlying) return undefined;
  const elaboration = selectedName
    ? `${notation.target}(${selectedName}, ${notation.fixity === "prefix" ? "·" : "·, ·"})`
    : notation.target;
  const display = notation.fixity === "mixfix" ? token.text.replaceAll("_", "·") : token.text;
  const unfoldHint = notation.fixity === "mixfix" ? `\nunfold ${underlying.name.split(".").at(-1)} unfolds it in a goal` : "";
  const shape = notationShape(notation, token.text, underlying);
  return {
    ...underlying,
    short: display,
    kind: `notation for ${underlying.kind}`,
    info: `${display} → ${elaboration}${unfoldHint}\n${underlying.info}`,
    notationTarget: underlyingName,
    written: shape.written,
    elaborated: shape.elaborated,
    declaration: underlying.info,
    module: symbolModule(underlying),
    token,
  };
}

// The written form of a notation and the application it elaborates to,
// with the parameters of the underlying declaration as the operands:
// `A ∩ B` and `intersection(A, B)` for a binary infix on `def intersection
// (A B : Set)`; placeholders stand in where the declaration names none.
function notationShape(notation, tokenText, underlying) {
  const short = underlying.name.split(".").at(-1);
  const declared = /\(([^():]*):/.exec(underlying.info || "");
  const names = declared ? declared[1].trim().split(/\s+/).filter(Boolean) : [];
  const operand = index => names[index] || ["a", "b", "c"][index] || `x${index + 1}`;
  const leading = notation.leadingArguments?.length || 0;
  const argument = index => operand(leading + index);
  switch (notation.fixity) {
    case "prefix": return { written: `${tokenText}${argument(0)}`, elaborated: `${short}(${argument(0)})` };
    case "postfix": return { written: `${argument(0)}${tokenText}`, elaborated: `${short}(${argument(0)})` };
    case "constant": return { written: tokenText, elaborated: short };
    case "mixfix": {
      const slots = tokenText.split("_").length - 1;
      const operands = Array.from({ length: slots }, (_, index) => argument(index));
      let position = 0;
      const written = tokenText.replace(/_/g, () => operands[position++]).replace(/\s+/g, " ").trim();
      return { written, elaborated: `${short}(${operands.join(", ")})` };
    }
    default:
      return { written: `${argument(0)} ${tokenText} ${argument(1)}`, elaborated: `${short}(${argument(0)}, ${argument(1)})` };
  }
}

// The module a symbol's full name lies in, as far as the loaded modules say.
function symbolModule(symbol) {
  if (symbol.module) return symbol.module;
  const modules = (result?.documents || []).map(item => item.module).filter(Boolean);
  const name = symbol.name || "";
  return modules.filter(module => name.startsWith(module + ".")).sort((a, b) => b.length - a.length)[0] || "";
}

// A token supplied by a hypothesis in scope, a⁻¹ for apply(G.inv, a) under
// Group(G): the hover shows the operation read off the hypothesis, names the
// hypotheses that supply it, and opens the projection behind it. Among
// several such forms, those whose hypothesis is in scope come first.
function hypothesisNotationSymbol(token, candidates, context) {
  if (!candidates.length) return undefined;
  const short = name => name.split(".").at(-1);
  const template = (term, predicate) => {
    if (!term) return "·";
    if (term.tag === "var") return term.name;
    if (term.tag !== "app") return "·";
    const projection = term.args.length === 1 && term.args[0].tag === "var" && term.fn.split(".").at(-2) === short(predicate);
    return projection ? `${term.args[0].name}.${short(term.fn)}` : `${short(term.fn)}(${term.args.map(item => template(item, predicate)).join(", ")})`;
  };
  const describe = item => `${short(item.hypothesis.predicate)}(${item.hypothesis.names.join(", ")})`;
  const inScope = item => {
    const spelled = `${short(item.hypothesis.predicate)}(`;
    return (context?.localSymbols || []).some(local => local.formula?.includes(spelled)) || source.value.includes(spelled);
  };
  const ordered = [...candidates.filter(inScope), ...candidates.filter(item => !inScope(item))];
  const head = item => item.hypothesis.output?.tag === "app" ? item.hypothesis.output.fn : item.target;
  const chosen = ordered.filter(item => head(item) === head(ordered[0]));
  const first = chosen[0];
  const operation = template(first.hypothesis.output, first.hypothesis.predicate);
  const display = first.fixity === "postfix" ? `a${token.text}` : first.fixity === "prefix" ? `${token.text}a`
    : first.fixity === "constant" ? token.text : first.structure ? `${first.hypothesis.names[0]} ${token.text} N` : `a ${token.text} b`;
  const elaboration = first.fixity === "postfix" || first.fixity === "prefix" ? `${first.target}(${operation}, a)`
    : first.fixity === "constant" ? operation : first.structure ? `${first.target}(${first.hypothesis.names[0]}, N)` : `${first.target}(${operation}, a, b)`;
  const suppliers = [...new Set(chosen.map(describe))].join(" or ");
  const underlyingName = head(first);
  const underlying = result?.symbols?.find(symbol => symbol.name === underlyingName);
  const info = `${display} → ${elaboration}\nsupplied by a hypothesis ${suppliers}${underlying ? `\n${underlying.info}` : ""}`;
  return underlying
    ? { ...underlying, short: display, kind: "notation supplied by a hypothesis", info, notationTarget: underlyingName, token }
    : { name: token.text, short: display, kind: "notation supplied by a hypothesis", info, ephemeral: true, token };
}

function localTypeAt(token) {
  return localTypeAtTextOffset(source.value, token);
}

function localSymbol(token) {
  const theoremIndex = theoremSelect.value === "" ? undefined : Number(theoremSelect.value);
  const theorem = Number.isSafeInteger(theoremIndex) ? result?.theorems?.[theoremIndex] : undefined;
  if (theorem) {
    const stages = [{ after: theorem.initial }, ...visibleTheoremSteps(theorem)];
    const state = stages[Math.min(selectedStep, stages.length - 1)]?.after;
    const local = state?.goals?.flatMap(goal => goal.locals).find(item => item.name === token.text);
    if (local) return { name: token.text, short: token.text, kind: "local hypothesis", info: `${token.text} : ${local.formula}`, token };
  }
  const type = localTypeAt(token);
  return type ? { name: token.text, short: token.text, kind: "local", info: `${token.text} : ${type}`, token } : undefined;
}

function goToDefinition(symbol) {
  if (!symbol?.line || !symbol.file) return;
  let file = files.find(item => item.name === symbol.file);
  const documentSource = symbol.document ?? result?.documents?.find(item => item.file === symbol.file);
  if (!file && documentSource) {
    file = files.find(item => moduleName(item.source, item.sourceFile || item.name) === documentSource.module);
    if (!file) {
      file = { id: makeId(), name: documentSource.name, source: documentSource.source, sourceFile: documentSource.file };
      files.push(file);
    }
  }
  if (!file) return;
  persistWorkspace();
  const changedFile = activeId !== file.id;
  activateFile(file.id, false);
  jumpToLine(symbol.line);
  setStatus(`Definition · ${symbol.short}`);
  if (changedFile) scheduleCheck(0);
}

function jumpToSorrySite(theorem, index) {
  const sites = theorem?.sorries || [];
  if (!sites.length) return;
  const safeIndex = Math.min(Math.max(0, index), sites.length - 1);
  const site = sites[safeIndex];
  let file = files.find(item => item.name === site.file);
  const documentSource = result?.documents?.find(item => item.file === site.file);
  if (!file && documentSource) {
    file = files.find(item => moduleName(item.source, item.sourceFile || item.name) === documentSource.module);
    if (!file) {
      file = { id: makeId(), name: documentSource.name, source: documentSource.source, sourceFile: documentSource.file };
      files.push(file);
    }
  }
  if (!file) return;
  persistWorkspace();
  activateFile(file.id, false);
  const model = editor.getModel();
  const line = Math.min(Math.max(1, site.line || 1), model.getLineCount());
  const match = /\bsorry\b/.exec(model.getLineContent(line));
  const startColumn = (match?.index ?? 0) + 1;
  const endColumn = startColumn + (match?.[0].length ?? 0);
  editor.setSelection(new monaco.Range(line, startColumn, line, endColumn));
  editor.revealLineInCenterIfOutsideViewport(line);
  editor.focus();
  setStatus(`sorry ${safeIndex + 1} of ${sites.length}`, "warning");
}

function moduleName(text, file = "") { return moduleNameOf(text, file); }

function escapeMarkdown(value) {
  return String(value).replaceAll("\\", "\\\\").replaceAll("`", "\\`").replaceAll("*", "\\*");
}

function configureGrace17Language() {
  monaco.languages.register({ id: "grace17", extensions: [".g17"], aliases: ["Grace17", "g17"] });
  monaco.languages.setLanguageConfiguration("grace17", {
    comments: { lineComment: "--" },
    brackets: [["(", ")"], ["[", "]"], ["{", "}"], ["⟨", "⟩"]],
    autoClosingPairs: [
      { open: "(", close: ")" }, { open: "[", close: "]" },
      { open: "{", close: "}" }, { open: "⟨", close: "⟩" },
    ],
    surroundingPairs: [
      { open: "(", close: ")" }, { open: "[", close: "]" },
      { open: "{", close: "}" }, { open: "⟨", close: "⟩" },
    ],
  });
  monaco.languages.setMonarchTokensProvider("grace17", {
    unicode: true,
    keywords: [
      "module", "import", "namespace", "section", "variable", "hypothesis", "export", "open", "end", "datatype", "structure", "self", "noncomputable",
      "transfinite", "foundation", "well-founded", "limit", "over", "ordered", "certified", "defgraph", "defchoose", "defunique", "uniqueness", "def", "define", "predicate", "class", "theorem", "lemma", "instance", "eval", "notation",
      "tactic", "infix", "infixl", "infixr", "mixfix", "prefix", "postfix", "guard", "scoped", "binder", "reverse", "requires", "shows", "proof", "where",
      "decreasing_by",
    ],
    connectives: ["at", "with", "by", "via", "for", "under", "using", "as"],
    tactics: [
      "settle", "simp", "ring", "ring_nf", "linear_combination", "arith", "linarith", "tauto", "cc", "congruence", "rewrite", "rw", "compute", "intro", "intros", "ext", "apply", "exact", "have", "specialize",
      "obtain", "unfold", "induction", "show", "symm", "constructor", "split", "refine", "witness", "use", "assumption", "calc",
      "contradiction", "exfalso", "by_contra", "clear", "rename", "revert", "rcases", "cases",
      "reflexivity", "rfl", "left", "right", "typecheck", "synthesize", "sorry",
    ],
    types: ["Set", "Nat", "Ordinal", "Class", "Prop", "ℕ"],
    tokenizer: {
      root: [
        [/--[!|].*$/, "comment.narrative"],
        [/--.*$/, "comment"],
        [/\b\d+\b/, "number"],
        [/[\p{L}_][\p{L}\p{M}\p{N}_'.?]*/u, { cases: { "@connectives": "keyword.connective", "@keywords": "keyword", "@tactics": "tactic", "@types": "type", "@default": "identifier" } }],
        [/[ℕ]/, "type"],
        [/[→←↔∈≤≥≠∅⊎≃↦×∫=+*<>^]|::|:=|=>|<-/, "operator"],
        [/[{}()[\]]/, "delimiter.bracket"],
      ],
    },
  });
  monaco.editor.defineTheme("grace17-dark", {
    base: "vs-dark",
    inherit: true,
    rules: [
      { token: "keyword", foreground: "57F4FF" },
      { token: "keyword.connective", foreground: "65AEF2" },
      { token: "tactic", foreground: "65AEF2" },
      { token: "type", foreground: "00C8D7" },
      { token: "number", foreground: "8BBEF0" },
      { token: "operator", foreground: "AAB8C0" },
      { token: "comment", foreground: "61737D", fontStyle: "italic" },
      { token: "comment.narrative", foreground: "65AEF2", fontStyle: "italic" },
      { token: "identifier", foreground: "D8E2E7" },
    ],
    colors: {
      "editor.background": "#000000",
      "editor.foreground": "#D8E2E7",
      "editorLineNumber.foreground": "#53646E",
      "editorLineNumber.activeForeground": "#AAB8C0",
      "editorCursor.foreground": "#57F4FF",
      "editor.selectionBackground": "#2C77C780",
      "editor.inactiveSelectionBackground": "#2C77C740",
      "editor.lineHighlightBackground": "#0D1B247F",
      "editorError.foreground": "#FF6565",
      "editorGutter.background": "#000000",
      "minimap.background": "#000000",
    },
  });
}

installLibrarySearch({
  getFiles: () => workspacePayload(),
  focusEditor: () => editor.focus(),
  navigate: hit => {
    let file = files.find(item => item.name === hit.file);
    if (!file && standardLibrary.has(hit.file)) {
      file = { id: makeId(), name: hit.file, source: standardLibrary.get(hit.file), sourceFile: hit.file };
      files.push(file);
    }
    if (file) goToDefinition({ ...hit, file: file.name });
  },
});

// Links open bundled source locally; they never replace an edited workspace file.
function openLinkedProof() {
  try {
    const target = resolveWorkbenchLink(location.href, standardLibrary);
    if (!target) return;
    let file = files.find(item => item.name === target.file);
    if (!file) {
      file = target.inline
        ? { id: makeId(), name: target.file, source: target.source, dirty: true, openedIn: WORKBENCH_VERSION }
        : { id: makeId(), name: target.file, source: target.source, sourceFile: target.file };
      files.push(file);
    } else if (target.inline && file.source !== target.source) {
      // A documentation link always shows the linked text, even over an edited buffer.
      file.source = target.source;
      file.dirty = true;
      const model = modelFor(file);
      if (model.getValue() !== target.source) model.setValue(target.source);
    }
    activateFile(file.id, false);
    const line = Math.min(target.line, file.source.split("\n").length);
    jumpToLine(line);
    settleLinkedLine(file.id, line);
    // A link may ask for the kernel proof view: the Fitch-style derivation
    // of the theorem at the linked line opens as soon as the check finishes.
    if (target.view === "kernel") { document.querySelector("#kernelDrawer").open = true; maximizeKernelOnRender = true; }
    prepareThenCheckActive();
  } catch (error) {
    setStatus(`Cannot open proof link: ${error.message}`);
    // A link to a module this build does not bundle is usually a link to a
    // newer build; the worker installing it will offer the reload.
    if (/not in the bundled library/.test(error.message)) offerUpdate("This link needs a newer version of the Workbench; reload to get it.");
  }
}

// A link's line is revealed again once the editor has its final layout and
// fonts, so a reveal issued before the first layout cannot be lost. The cursor
// is left alone if the reader has already moved it.
function settleLinkedLine(fileId, line) {
  const settle = () => {
    if (activeId !== fileId || editor.getPosition()?.lineNumber !== line) return;
    editor.revealLineInCenter(line);
  };
  requestAnimationFrame(settle);
  setTimeout(settle, 400);
  const layout = editor.onDidLayoutChange(() => { settle(); layout.dispose(); });
  document.fonts?.ready?.then(settle);
}
openLinkedProof();
window.addEventListener("hashchange", openLinkedProof);
