// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Search has its own worker so checking a long proof cannot block discovery.
import { standardLibrary } from "./generated/shims/standard-library.js";
import { LibrarySearchWorkspace } from "./library-search.js";
const workspace = new LibrarySearchWorkspace(standardLibrary);
self.addEventListener("message", ({ data }) => {
  try {
    if (data.files) workspace.sync(data.files);
    self.postMessage({ id: data.id, result: workspace.index.search(String(data.query || "")) });
  } catch (error) { self.postMessage({ id: data.id, error: error.message }); }
});
