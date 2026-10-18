// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

const scope = new URL("./", self.location.href);
const cachePrefix = `grace17-workbench-${scope.pathname}-`;
const cacheName = `${cachePrefix}v__GRACE17_VERSION__`;
const scoped = path => new URL(path.replace(/^\//, ""), scope).href;
const localWorkbench = ["127.0.0.1", "localhost", "[::1]"].includes(self.location.hostname);
const shell = [
  "/", "/index.html", "/styles.css", "/bootstrap.js", "/app.js", "/editor-utils.js", "/module-navigation.js", "/axiom-audit.js", "/tactics-guide.js",
  "/deep-links.js", "/library-search.js", "/library-search-worker.js", "/library-search-ui.js",
  "/worker-client.js", "/browser-worker.js", "/manifest.webmanifest",
  "/generated/shims/standard-library.js",
  "/generated/version.js",
  "/assets/grace-icon.svg", "/assets/grace17-wordmark-dark.svg", "/assets/qed-mark.svg", "/assets/qed-mark-sorry.svg",
  "/generated/monaco/vs/loader.js", "/generated/monaco/vs/editor/editor.main.js", "/generated/monaco/vs/editor/editor.main.css"
];

self.addEventListener("install", event => {
  if (localWorkbench) {
    self.skipWaiting();
    return;
  }
  // Installing fetches past the HTTP cache: the host serves files with a
  // short freshness lifetime, and a new build must not be assembled from a
  // stale copy of an old one.
  const fresh = path => new Request(scoped(path), { cache: "reload" });
  event.waitUntil(caches.open(cacheName).then(async cache => {
    await cache.addAll(shell.map(fresh));
    const response = await fetch(fresh("generated/monaco-assets.json"));
    const cachedManifest = response.clone();
    const assets = await response.json();
    await cache.put(scoped("generated/monaco-assets.json"), cachedManifest);
    await cache.addAll(assets.map(fresh));
  }));
  self.skipWaiting();
});

self.addEventListener("activate", event => {
  event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key =>
    key.startsWith(cachePrefix) && (localWorkbench || key !== cacheName)).map(key => caches.delete(key)))));
  self.clients.claim();
});

self.addEventListener("fetch", event => {
  if (event.request.method !== "GET") return;
  if (!event.request.url.startsWith(scope.href)) return;
  if (localWorkbench) {
    event.respondWith(fetch(event.request, { cache: "no-store" }));
    return;
  }
  // Only this build's cache answers; a miss is revalidated with the server
  // rather than taken from the HTTP cache of an earlier build.
  event.respondWith(caches.open(cacheName).then(cache => cache.match(event.request)).then(cached => cached || fetch(new Request(event.request, { cache: "no-cache" })).then(response => {
    if (!response.ok) return response;
    const copy = response.clone();
    caches.open(cacheName).then(cache => cache.put(event.request, copy));
    return response;
  })));
});
