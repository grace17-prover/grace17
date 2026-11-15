// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { connect } from "node:net";
import { createInterface } from "node:readline";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { MACHINE_PROTOCOL_VERSION } from "../src/index.ts";

const project = join(dirname(fileURLToPath(import.meta.url)), "..");

test("g17 serve --port answers the stdio protocol over a loopback TCP connection", async () => {
  const serve = spawn(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "serve", "--port", "0"],
    { cwd: project, stdio: ["ignore", "pipe", "pipe"] });
  try {
    const started = createInterface({ input: serve.stdout })[Symbol.asyncIterator]();
    const first = JSON.parse((await started.next()).value as string);
    assert.equal(first.version, MACHINE_PROTOCOL_VERSION);
    assert.equal(first.listening.host, "127.0.0.1");
    assert.ok(Number.isInteger(first.listening.port) && first.listening.port > 0);
    const socket = connect(first.listening.port, first.listening.host);
    const lines = createInterface({ input: socket })[Symbol.asyncIterator]();
    const ask = async (request: unknown): Promise<any> => {
      socket.write(`${JSON.stringify(request)}\n`);
      return JSON.parse((await lines.next()).value as string);
    };
    const source = "module Probe\n\ntheorem probe (x : Set)\n  shows x = x\nproof\n  rfl\n";
    const checked = await ask({ id: 1, method: "check", params: { files: [{ name: "Probe.g17", source }] } });
    assert.equal(checked.ok, true, JSON.stringify(checked.error));
    assert.equal(checked.result.status, "checked");
    assert.deepEqual(checked.result.theorems.map((item: { status: string }) => item.status), ["proved"]);
    const malformed = await ask("not an object");
    assert.equal(malformed.ok, false);
    assert.equal(malformed.error.code, "invalid_request");
    const capabilities = await ask({ id: 2, method: "capabilities" });
    assert.equal(capabilities.result.protocol, MACHINE_PROTOCOL_VERSION);
    await new Promise<void>(resolve => { socket.once("close", () => resolve()); socket.end(); });
  } finally {
    const exited = new Promise<void>(resolve => serve.once("exit", () => resolve()));
    serve.kill("SIGTERM");
    await exited;
  }
});
