// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

const base = new URL("./", document.currentScript.src);
globalThis.require.config({ paths: { vs: new URL("generated/monaco/vs", base).href } });
globalThis.require(["vs/editor/editor.main"], () => import(new URL("app.js", base).href));
