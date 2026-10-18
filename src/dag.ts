// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { sha256Hex } from "./hash.ts";
import { canonical, type Formula } from "./ast.ts";
import { KernelError, type Kernel, type ProofCheckStats } from "./kernel.ts";
import type { Proof } from "./proof.ts";

interface ProofReference {
  readonly $proof: number;
}

export interface ProofDagNode {
  readonly payload: unknown;
}

export interface ProofDag {
  readonly version: 1;
  readonly nodes: readonly ProofDagNode[];
  readonly root: number;
  readonly digest: string;
}

export interface CheckedProofDag {
  readonly formula: Formula;
  readonly stats: ProofCheckStats;
  readonly dagNodes: number;
  readonly treeNodes: number;
}

export interface IndexedProofDag {
  readonly dag: ProofDag;
  readonly nodeIds: ReadonlyMap<Proof, number>;
}

/** Convert a proof tree to a deterministic, structurally hash-consed DAG. */
export function encodeProofDag(proof: Proof): ProofDag {
  return encodeProofDagWithIndex(proof).dag;
}

/** Encode a proof and retain the object-to-node correspondence for diagnostics. */
export function encodeProofDagWithIndex(proof: Proof): IndexedProofDag {
  const nodes: ProofDagNode[] = [];
  const interned = new Map<string, number>();
  const nodeIds = new Map<Proof, number>();

  const encodeValue = (value: unknown): unknown => {
    if (isProof(value)) return { $proof: intern(value) } satisfies ProofReference;
    if (Array.isArray(value)) return value.map(encodeValue);
    if (value !== null && typeof value === "object") {
      return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, encodeValue(child)]));
    }
    return value;
  };
  const intern = (item: Proof): number => {
    // Proofs share subderivations. Consult identity before traversing children;
    // structural interning alone still unfolds the shared tree exponentially.
    const known = nodeIds.get(item);
    if (known !== undefined) return known;
    const payload = Object.fromEntries(Object.entries(item).map(([key, value]) => [key, encodeValue(value)]));
    const key = canonical(payload);
    const previous = interned.get(key);
    if (previous !== undefined) {
      nodeIds.set(item, previous);
      return previous;
    }
    const id = nodes.length;
    nodes.push(Object.freeze({ payload }));
    interned.set(key, id);
    nodeIds.set(item, id);
    return id;
  };

  const root = intern(proof);
  const body = { version: 1 as const, nodes, root };
  const digest = sha256Hex(canonical(body));
  const dag = Object.freeze({ ...body, nodes: Object.freeze([...nodes]), digest });
  return { dag, nodeIds };
}

/**
 * Authenticate and replay a compact proof tape.
 *
 * Nodes are stored in postorder and may only refer backwards.  Decoding keeps
 * shared object identity, so the kernel executes each (proof, context) pair at
 * most once.  This is the GRACE17 analogue of Metamath's RPN proof stack and
 * compressed-proof saved steps.
 */
export function checkProofDag(
  kernel: Kernel,
  dag: ProofDag,
  assumptions: readonly Formula[] = [],
): CheckedProofDag {
  const body = { version: dag.version, nodes: dag.nodes, root: dag.root };
  const digest = sha256Hex(canonical(body));
  if (dag.version !== 1 || digest !== dag.digest) throw new KernelError("Malformed or corrupted proof DAG");
  if (!Number.isSafeInteger(dag.root) || dag.root < 0 || dag.root >= dag.nodes.length) {
    throw new KernelError("Proof DAG has an invalid root");
  }
  const decoded = decodeProofDag(dag);
  const root = decoded[dag.root]!;
  const checked = kernel.checkProofWithStats(root, assumptions);
  return {
    formula: checked.formula,
    stats: checked.stats,
    dagNodes: dag.nodes.length,
    // Compute this presentation statistic over the compact tape.  Expanding
    // the decoded DAG here used to make checking appear exponentially slow.
    treeNodes: countProofDagTree(dag),
  };
}

/** Count the represented proof tree in O(number of tape nodes). */
export function countProofDagTree(dag: ProofDag): number {
  const counts: number[] = [];
  const references = (value: unknown, current: number): number => {
    if (isReference(value)) {
      if (!Number.isSafeInteger(value.$proof) || value.$proof < 0 || value.$proof >= current) {
        throw new KernelError("Proof DAG contains a forward or cyclic reference");
      }
      return counts[value.$proof]!;
    }
    if (Array.isArray(value)) return value.reduce((sum, child) => saturatingAdd(sum, references(child, current)), 0);
    if (value !== null && typeof value === "object") {
      return Object.values(value).reduce((sum, child) => saturatingAdd(sum, references(child, current)), 0);
    }
    return 0;
  };
  dag.nodes.forEach((node, index) => counts.push(saturatingAdd(1, references(node.payload, index))));
  return counts[dag.root] ?? 0;
}

function saturatingAdd(left: number, right: number): number {
  const result = left + right;
  return Number.isSafeInteger(result) ? result : Number.MAX_SAFE_INTEGER;
}

/** Reconstruct proof nodes after the DAG envelope has been authenticated. */
export function decodeProofDag(dag: ProofDag): readonly Proof[] {
  const decoded: Proof[] = [];
  const decodeValue = (value: unknown, current: number): unknown => {
    if (isReference(value)) {
      if (!Number.isSafeInteger(value.$proof) || value.$proof < 0 || value.$proof >= current) {
        throw new KernelError("Proof DAG contains a forward or cyclic reference");
      }
      return decoded[value.$proof]!;
    }
    if (Array.isArray(value)) return value.map(child => decodeValue(child, current));
    if (value !== null && typeof value === "object") {
      return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, decodeValue(child, current)]));
    }
    return value;
  };
  dag.nodes.forEach((node, index) => {
    const value = decodeValue(node.payload, index);
    if (!isProof(value)) throw new KernelError(`Proof DAG node ${index} is not a proof`);
    decoded.push(value);
  });
  return decoded;
}

export function countProofTree(proof: Proof): number {
  const visit = (value: unknown): number => {
    if (isProof(value)) {
      return 1 + Object.entries(value)
        .filter(([key]) => key !== "rule")
        .reduce((sum, [, child]) => sum + visit(child), 0);
    }
    if (Array.isArray(value)) return value.reduce((sum, child) => sum + visit(child), 0);
    if (value !== null && typeof value === "object") {
      return Object.values(value).reduce((sum, child) => sum + visit(child), 0);
    }
    return 0;
  };
  return visit(proof);
}

function isProof(value: unknown): value is Proof {
  return value !== null && typeof value === "object" && typeof (value as { rule?: unknown }).rule === "string";
}

function isReference(value: unknown): value is ProofReference {
  return value !== null && typeof value === "object" &&
    Object.keys(value).length === 1 && typeof (value as { $proof?: unknown }).$proof === "number";
}
