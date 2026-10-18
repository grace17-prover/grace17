#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { createReadStream, existsSync, readFileSync, statSync } from "node:fs";
import { createServer, type IncomingMessage, type ServerResponse } from "node:http";
import { extname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { auditWorkbenchTheorem, checkWorkbenchFiles, runWorkbenchFiles, workbenchFailure, type WorkbenchFile } from "../src/workbench.ts";

const root = fileURLToPath(new URL("../workbench", import.meta.url));
const version = JSON.parse(readFileSync(fileURLToPath(new URL("../package.json", import.meta.url)), "utf8")).version as string;
const requestedPort = Number(process.env.GRACE17_PORT ?? "1717");
const port = Number.isSafeInteger(requestedPort) && requestedPort > 0 ? requestedPort : 1717;
const mime = new Map([
  [".html", "text/html; charset=utf-8"], [".js", "text/javascript; charset=utf-8"], [".css", "text/css; charset=utf-8"],
  [".svg", "image/svg+xml"], [".webmanifest", "application/manifest+json"], [".json", "application/json; charset=utf-8"],
]);

const server = createServer(async (request, response) => {
  try {
    if (request.method === "POST" && request.url === "/api/axiom-audit") {
      const body = await readJson(request);
      const files = workspaceFiles(body);
      return json(response, 200, auditWorkbenchTheorem(files, String(body.theorem ?? ""), "ZFG", activeEntry(body, files)));
    }
    if (request.method === "POST" && request.url === "/api/check") {
      const body = await readJson(request);
      const files = workspaceFiles(body);
      return json(response, 200, checkWorkbenchFiles(files, "ZFG", activeEntry(body, files)));
    }
    if (request.method === "POST" && request.url === "/api/run") {
      const body = await readJson(request);
      const rawArgs = Array.isArray(body.args) ? body.args : String(body.args ?? "").split(",").filter(Boolean);
      const args = rawArgs.map(value => {
        const text = String(value).trim();
        if (!/^\d+$/.test(text)) throw new Error("Run arguments must be natural numerals");
        return BigInt(text);
      });
      const files = workspaceFiles(body);
      return json(response, 200, runWorkbenchFiles(files, String(body.function ?? ""), args, "ZFG", activeEntry(body, files)));
    }
    if (request.method !== "GET") return json(response, 405, { ok: false, message: "Method not allowed" });
    const requestUrl = new URL(request.url ?? "/", "http://localhost");
    if (requestUrl.pathname === "/" && requestUrl.searchParams.get("fresh") === version) {
      return freshWorkbench(response, version);
    }
    const pathname = requestUrl.pathname === "/" ? "/index.html" : requestUrl.pathname;
    const file = resolve(root, `.${pathname}`);
    if (!file.startsWith(`${root}/`) || !existsSync(file) || !statSync(file).isFile()) return json(response, 404, { ok: false, message: "Not found" });
    response.writeHead(200, { "content-type": mime.get(extname(file)) ?? "application/octet-stream", "cache-control": "no-store" });
    createReadStream(file).pipe(response);
  } catch (error) {
    json(response, 400, workbenchFailure(error));
  }
});

server.listen(port, "127.0.0.1", () => {
  console.log(`GRACE17 Workbench ${version} → http://127.0.0.1:${port}/?fresh=${encodeURIComponent(version)}`);
  console.log("Press Ctrl+C to stop.");
});

function freshWorkbench(response: ServerResponse, currentVersion: string): void {
  const next = `/?version=${encodeURIComponent(currentVersion)}`;
  const html = `<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Starting Grace17 ${currentVersion}</title><body style="margin:0;background:#080d16;color:#59e1d0;font:14px ui-monospace,monospace;display:grid;place-items:center;min-height:100vh">Starting Grace17 ${currentVersion}…<script>(async()=>{if("serviceWorker" in navigator){const registrations=await navigator.serviceWorker.getRegistrations();await Promise.all(registrations.map(item=>item.unregister()))}if("caches" in globalThis){const names=await caches.keys();await Promise.all(names.filter(name=>name.startsWith("grace17-workbench-")).map(name=>caches.delete(name)))}location.replace(${JSON.stringify(next)})})()</script></body>`;
  response.writeHead(200, { "content-type": "text/html; charset=utf-8", "cache-control": "no-store" });
  response.end(html);
}

function workspaceFiles(body: Record<string, unknown>): WorkbenchFile[] {
  if (!Array.isArray(body.files)) return [{ name: "Playground.g17", source: String(body.source ?? "") }];
  if (body.files.length === 0 || body.files.length > 64) throw new Error("A workspace must contain between 1 and 64 files");
  let total = 0;
  return body.files.map((value, index) => {
    if (value === null || typeof value !== "object") throw new Error(`Malformed workspace file #${index + 1}`);
    const item = value as Record<string, unknown>;
    const name = String(item.name ?? "");
    const source = String(item.source ?? "");
    if (!name || name.includes("\0")) throw new Error(`Workspace file #${index + 1} needs a name`);
    total += Buffer.byteLength(source);
    if (total > 1_000_000) throw new Error("Workspace source is too large");
    return { name, source };
  });
}

function activeEntry(body: Record<string, unknown>, files: readonly WorkbenchFile[]): readonly string[] | undefined {
  if (body.activeFile === undefined) return undefined;
  const active = String(body.activeFile);
  if (!files.some(file => file.name === active)) throw new Error(`Unknown active workspace file ${active}`);
  return [active];
}

async function readJson(request: IncomingMessage): Promise<Record<string, unknown>> {
  const chunks: Buffer[] = [];
  let size = 0;
  for await (const chunk of request) {
    const value = Buffer.from(chunk);
    size += value.length;
    if (size > 1_000_000) throw new Error("Request is too large");
    chunks.push(value);
  }
  return JSON.parse(Buffer.concat(chunks).toString("utf8") || "{}");
}

function json(response: ServerResponse, status: number, value: unknown): void {
  response.writeHead(status, { "content-type": "application/json; charset=utf-8", "cache-control": "no-store" });
  response.end(JSON.stringify(value));
}
