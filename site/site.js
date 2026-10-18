// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Copy buttons for code blocks and the current-page marker in navigation.
for (const button of document.querySelectorAll("button.copy")) {
  button.addEventListener("click", async () => {
    const code = button.closest("figure")?.querySelector("pre")?.innerText ?? "";
    try { await navigator.clipboard.writeText(code); button.textContent = "Copied"; }
    catch { button.textContent = "Select and copy"; }
    setTimeout(() => { button.textContent = "Copy"; }, 1400);
  });
}
const here = new URL(location.href);
for (const link of document.querySelectorAll(".site-nav a, .sidebar a")) {
  const target = new URL(link.getAttribute("href"), here);
  if (target.pathname === here.pathname || target.pathname + "index.html" === here.pathname) link.setAttribute("aria-current", "page");
}
// Collapse the documentation sidebar on narrow screens; it is a toggle there.
const sidebarDetails = document.querySelector(".sidebar details");
if (sidebarDetails && window.matchMedia("(max-width: 860px)").matches) sidebarDetails.open = false;

// Hover cards for inline code that names a library declaration.
import { highlightGrace17 } from "./workbench/tactics-guide.js";
let card;
function showCard(link) {
  if (!card) { card = document.createElement("div"); card.className = "decl-card"; card.setAttribute("role", "tooltip"); document.body.append(card); }
  card.innerHTML = `<div class="decl-card-head">${link.dataset.module}</div><pre><code>${highlightGrace17(link.dataset.signature)}</code></pre><small>${"several" in link.dataset ? "Click to search the library for this name" : "Click to open the source"}</small>`;
  placeCard(link);
}
function placeCard(anchor) {
  const rect = anchor.getBoundingClientRect();
  card.hidden = false;
  const width = Math.min(560, window.innerWidth - 24);
  card.style.width = `${width}px`;
  card.style.left = `${Math.max(12, Math.min(rect.left, window.innerWidth - width - 12))}px`;
  const below = rect.bottom + 8;
  card.style.top = `${below + card.offsetHeight > window.innerHeight ? Math.max(8, rect.top - card.offsetHeight - 8) : below}px`;
}
// Prose notes: a span with data-note shows its text in the same card.
function showNote(span) {
  if (!card) { card = document.createElement("div"); card.className = "decl-card"; card.setAttribute("role", "tooltip"); document.body.append(card); }
  card.textContent = "";
  const text = document.createElement("p");
  text.className = "decl-card-note";
  text.textContent = span.dataset.note;
  card.append(text);
  placeCard(span);
}
for (const link of document.querySelectorAll("a.decl")) {
  link.addEventListener("mouseenter", () => showCard(link));
  link.addEventListener("focus", () => showCard(link));
  link.addEventListener("mouseleave", () => { if (card) card.hidden = true; });
  link.addEventListener("blur", () => { if (card) card.hidden = true; });
}
// Profile links: the person's photo, name, and page in the same card.
function showProfile(link) {
  if (!card) { card = document.createElement("div"); card.className = "decl-card"; card.setAttribute("role", "tooltip"); document.body.append(card); }
  card.textContent = "";
  const row = document.createElement("div");
  row.className = "decl-card-profile";
  if (link.dataset.photo) {
    const photo = document.createElement("img");
    photo.src = link.dataset.photo;
    photo.alt = "";
    row.append(photo);
  }
  const text = document.createElement("div");
  const name = document.createElement("strong");
  name.textContent = link.dataset.name;
  text.append(name);
  if (link.dataset.line) {
    const line = document.createElement("small");
    line.textContent = link.dataset.line;
    text.append(line);
  }
  // The address is stored encoded and decoded only into the card, so the
  // page source never carries it as text.
  if (link.dataset.contact) {
    const contact = document.createElement("small");
    try { contact.textContent = atob(link.dataset.contact); } catch { contact.textContent = ""; }
    if (contact.textContent) text.append(contact);
  }
  row.append(text);
  card.append(row);
  placeCard(link);
}
for (const link of document.querySelectorAll("a.profile[data-name]")) {
  link.addEventListener("mouseenter", () => showProfile(link));
  link.addEventListener("focus", () => showProfile(link));
  link.addEventListener("mouseleave", () => { if (card) card.hidden = true; });
  link.addEventListener("blur", () => { if (card) card.hidden = true; });
}
for (const span of document.querySelectorAll(".note[data-note]")) {
  span.addEventListener("mouseenter", () => showNote(span));
  span.addEventListener("focus", () => showNote(span));
  span.addEventListener("mouseleave", () => { if (card) card.hidden = true; });
  span.addEventListener("blur", () => { if (card) card.hidden = true; });
}

// A link into a collapsible section (a tactic, a derivation line) opens it.
function openTarget() {
  const id = decodeURIComponent(location.hash.slice(1));
  if (!id) return;
  const target = document.getElementById(id);
  if (!target) return;
  for (let node = target; node; node = node.parentElement) if (node.tagName === "DETAILS") node.open = true;
  target.scrollIntoView({ block: "start" });
}
window.addEventListener("hashchange", openTarget);
openTarget();

// The contact address is assembled here rather than written into the page,
// so it is not harvested from the HTML.
for (const link of document.querySelectorAll("a.mail[data-user][data-host]")) {
  const address = `${link.dataset.user}@${link.dataset.host}`;
  link.href = `mailto:${address}`;
  link.textContent = address;
}
