#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Serve the built site from build/site with `cache-control: no-store`, so a
// rebuilt bundle is what the browser runs after a reload. A generic static
// server sends only Last-Modified, which browsers cache heuristically, and a
// hard reload does not refetch the module scripts a worker imports.
//
//   node scripts/serve-site.ts            # http://127.0.0.1:8017/
//   GRACE17_SITE_PORT=9000 node scripts/serve-site.ts

import { createReadStream, existsSync, statSync } from "node:fs";
import { createServer } from "node:http";
import { extname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../build/site", import.meta.url));
const port = Number(process.env.GRACE17_SITE_PORT ?? "8017");
const mime = new Map<string, string>([
  [".html", "text/html; charset=utf-8"], [".js", "text/javascript; charset=utf-8"], [".mjs", "text/javascript; charset=utf-8"],
  [".css", "text/css; charset=utf-8"], [".json", "application/json; charset=utf-8"], [".svg", "image/svg+xml"],
  [".png", "image/png"], [".webmanifest", "application/manifest+json"], [".wasm", "application/wasm"],
  [".ttf", "font/ttf"], [".woff", "font/woff"], [".woff2", "font/woff2"], [".g17", "text/plain; charset=utf-8"],
  [".map", "application/json"], [".txt", "text/plain; charset=utf-8"],
]);

createServer((request, response) => {
  const pathname = decodeURIComponent(new URL(request.url ?? "/", "http://localhost").pathname);
  let file = resolve(root, `.${pathname}`);
  if (!file.startsWith(root)) { response.writeHead(403); response.end(); return; }
  if (existsSync(file) && statSync(file).isDirectory()) file = resolve(file, "index.html");
  if (!existsSync(file) || !statSync(file).isFile()) { response.writeHead(404, { "cache-control": "no-store" }); response.end("Not found"); return; }
  response.writeHead(200, { "content-type": mime.get(extname(file)) ?? "application/octet-stream", "cache-control": "no-store" });
  createReadStream(file).pipe(response);
}).listen(port, "127.0.0.1", () => {
  console.log(`Serving ${root} at http://127.0.0.1:${port}/ with cache-control: no-store`);
});
