// Incremental local declaration search. Retrieval never establishes a proof.
// Copyright (c) 2026 Grant Passmore. Apache License 2.0.
// The implementation is src/library-search.ts, shared with the command line
// and the machine interface; the browser loads its generated copy.
export { LibrarySearchIndex, LibrarySearchWorkspace, matchesSourcePattern, moduleNameOf, parseSearchQuery, scanSearchDeclarations } from "./generated/src/library-search.js";
