#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const file = fileURLToPath(new URL("../lib/Grace/Cumulus/NumberTheory/Prime.g17", import.meta.url));
const name = "NumberTheory/Prime.g17";
const files = [{ name, source: readFileSync(file, "utf8") }];

const cold = checkWorkbenchFiles(files, "ZFG", [name], { includeKernelDetails: false });
const warm = checkWorkbenchFiles(files, "ZFG", [name], { includeKernelDetails: false });
const details = checkWorkbenchFiles(files, "ZFG", [name], { includeKernelDetails: true });

console.log("Workbench benchmark · Cumulus NumberTheory/Prime.g17");
console.log(`cold dependency elaboration + leaf  ${cold.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`warm active-leaf check              ${warm.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`on-demand kernel detail             ${details.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`${warm.theorems.length} displayed theorems · ${details.theorems.reduce((sum, theorem) => sum + theorem.judgments, 0)} checked judgments`);
