// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { app, bottom, createZfgKernel, eq, compileProofMachine, verifyProofMachine, exportTheorem, type Formula, type Proof, type ProofMachineModuleProgram } from '../src/index.ts';

function openFalse(kernel: ReturnType<typeof createZfgKernel>): ProofMachineModuleProgram {
  return { version: 4, environment: kernel.digest(), symbols: ['audit.false'], terms: [],
    formulas: [[0]], contexts: [[0], []], code: [[0,0,0,0,0]], root: 0, theorems: [[0,0]] };
}

test('open machine root cannot admit false, and failed batch is atomic', () => {
  const kernel = createZfgKernel();
  const digest = kernel.digest();
  const program = openFalse(kernel);
  assert.throws(() => verifyProofMachine(kernel, program), /empty contexts/);
  assert.throws(() => kernel.addTheoremMachineBatch([{name:'audit.false', statement:bottom}],program), /empty contexts/);
  assert.equal(kernel.theorems.has('audit.false'),false);
  assert.equal(kernel.digest(),digest);
});

test('a closed citation cannot launder an open theorem boundary', () => {
  const kernel=createZfgKernel();
  const program={...openFalse(kernel),code:[[0,0,0,0,0],[2,0,1,0,0]],root:1};
  assert.throws(()=>kernel.addTheoremMachineBatch([{name:'audit.false',statement:bottom}],program), /empty contexts/);
  assert.equal(kernel.theorems.has('audit.false'),false);
});

test('admission freezes separately allocated theorem and axiom statements deeply', () => {
  const kernel=createZfgKernel();
  const statement=structuredClone(eq(app('zero'),app('zero')));
  kernel.addTheorem('audit.refl',statement,{rule:'refl',term:app('zero')});
  assert.throws(()=>{(statement as {tag:string}).tag='bottom';},TypeError);
  assert.equal(Object.isFrozen((statement as any).left.args),true);
  const axiom=structuredClone(statement);
  kernel.addAxiom('audit.axiom',axiom);
  assert.throws(()=>{(axiom as {tag:string}).tag='bottom';},TypeError);
});

test('successful children of failed checks are immutable before cache retention', () => {
  const kernel=createZfgKernel();
  const child={rule:'refl',term:{tag:'app',fn:'zero',args:[]}} as Proof;
  const failed={rule:'andIntro',left:child,right:{rule:'assumption',formula:bottom}} as Proof;
  assert.throws(()=>kernel.checkProof(failed));
  assert.equal(Object.isFrozen(child),true);
  assert.equal(Object.isFrozen((child as any).term.args),true);
  assert.throws(()=>{(child as any).rule='assumption';},TypeError);
  assert.deepEqual(kernel.checkProof(child),eq(app('zero'),app('zero')));
});

test('shallow-frozen machine programs acquire deep immutability before reuse', () => {
  const kernel=createZfgKernel();
  kernel.addTheorem('audit.refl',eq(app('zero'),app('zero')),{rule:'refl',term:app('zero')});
  const program=structuredClone(compileProofMachine(exportTheorem(kernel,'audit.refl')));
  Object.freeze(program);
  verifyProofMachine(kernel,program);
  assert.equal(Object.isFrozen(program.code[0]),true);
  assert.throws(()=>{(program.code[0] as number[])[1]=999;},TypeError);
  verifyProofMachine(kernel,program);
});

test('definition input bodies and recursive admission payloads are deeply frozen', () => {
  const kernel=createZfgKernel();
  const body={tag:'app',fn:'zero',args:[]} as const;
  kernel.defineFunction('audit.zero',[],body);
  assert.equal(Object.isFrozen(body.args),true);
  assert.throws(()=>{(body as any).fn='succ';},TypeError);
});


test('mutable machine input never reuses a stale reified conclusion', () => {
  const kernel=createZfgKernel();
  const program={version:4 as const,environment:kernel.digest(),symbols:['zero','omega'],
    terms:[[2,0],[2,1]],formulas:[[1,0,0],[1,1,1]],contexts:[[]],
    code:[[4,0,0,0,0]],root:0};
  assert.deepEqual(verifyProofMachine(kernel,program).formula,eq(app('zero'),app('zero')));
  program.code[0]=[4,1,0,0,1];
  assert.deepEqual(verifyProofMachine(kernel,program).formula,eq(app('omega'),app('omega')));
});


test('Python G17C batch replay rejects false exports before admission', () => {
  const result=spawnSync('python3',['-c',`
import sys
from pathlib import Path
sys.path.insert(0, 'checkers/python')
from g17check import Program, Environment, verify, CheckError
env = Environment(Path('conformance/environment.g17env'))
for code, root in [([[0,0,0,0,0]],0), ([[0,0,0,0,0],[2,0,1,0,0]],1)]:
    program = Program(env.digest, ['audit.false'], [], [[0]], [[0],[]], code, root, [[0,0]])
    try:
        verify(program, env, False, {'audit.false': {'tag':'bottom'}})
    except CheckError as error:
        assert 'empty contexts' in str(error)
    else:
        raise AssertionError('false theorem batch accepted')
`],{cwd:fileURLToPath(new URL('..',import.meta.url)),encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);
});
