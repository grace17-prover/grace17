// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Test inputs produced by TypeScript; OCaml checks them independently.
import { mkdirSync, writeFileSync } from 'node:fs';
import { resolve, join } from 'node:path';
import {
  and, andIntro, app, assume, axiom, bind, canonical, compileKernelModule,
  compileSeparateKernelModule, compute, constructFoundation, ctor, describeFoundation,
  encodeProofMachineBinary, compileProofMachine, eq, existsIntro, exportKernelEnvironment,
  exportTheorem, forall, forallIntro, imp, impIntro, nat, pred, refl, substituteFormula, v,
} from '../src/index.ts';
const output=resolve(process.argv[2]??'build/ocaml-fixtures');
mkdirSync(output,{recursive:true});
const save=(name:string,value:unknown)=>writeFileSync(join(output,name),canonical(value)+'\n');
for(const profile of ['ZF','ZFC','ZFG'] as const){
  const base=constructFoundation(profile), source=base.fork(), checkpoint=source.admissionCheckpoint();
  source.addTheorem('fixture.reflexivity',eq(app('empty'),app('empty')),refl(app('empty')));
  save(`${profile}.g17f`,describeFoundation(profile));
  save(`${profile}.g17c`,compileSeparateKernelModule(base,base,source,checkpoint,{module:`Fixture.${profile}`}));
}
const base=constructFoundation('ZFG'), source=base.fork(), checkpoint=source.admissionCheckpoint();
source.defineFunction('identity',['x'],v('x'));
const relation=eq(v('value'),v('x'));
const premise=eq(v('other'),v('x'));
const existsUnique=forallIntro('x',existsIntro('value',and(relation,
  forall('other',imp(substituteFormula(relation,'value',v('other')),eq(v('other'),v('value'))))),
  v('x'),andIntro(refl(v('x')),forallIntro('other',impIntro(premise,assume(premise))))));
source.defineUniqueFunction({name:'selected',parameters:['x'],value:'value',relation,existsUnique});
const member=pred('in',v('x'),app('omega'));
// identity unfolds to x; use its equation to transport the closure proof.
import { eqElim, forallElim, definition } from '../src/index.ts';
const closure=forallIntro('x',impIntro(member,eqElim(
  forallElim(definition('identity'),v('x')),'z',pred('in',v('z'),app('omega')),assume(member),true)));
source.reifyUnaryOperation({name:'IdentityGraph',operation:'identity',domain:app('omega'),codomain:app('omega'),variable:'x',closure});
source.defineStructuralFunction({name:'plus',parameters:['x','y'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero'),bind('y')],body:v('y')},
  {patterns:[ctor('succ',bind('x')),bind('y')],body:app('succ',app('plus',v('x'),v('y')))},
]});
source.defineStructuralFunction({name:'times',parameters:['x','y'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero'),bind('y')],body:app('zero')},
  {patterns:[ctor('succ',bind('x')),bind('y')],body:app('plus',v('y'),app('times',v('x'),v('y')))},
]});
source.defineStructuralFunction({name:'factorial',parameters:['x'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero')],body:nat(1)},
  {patterns:[ctor('succ',bind('x'))],body:app('times',app('succ',v('x')),app('factorial',v('x')))},
]});
source.defineStructuralFunction({name:'shiftedProduct',parameters:['x','y'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero'),bind('y')],body:app('zero')},
  {patterns:[ctor('succ',bind('x')),bind('y')],body:app('plus',app('succ',v('y')),app('shiftedProduct',v('x'),v('y')))},
]});
source.defineStructuralFunction({name:'stack',parameters:['n'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero')],body:app('empty')},
  {patterns:[ctor('succ',bind('n'))],body:app('pair',app('empty'),app('stack',v('n')))},
]});
// Changing another argument used to force repeated prefix evaluation in the
// independent checkers. This recursion matches no arithmetic schema.
source.defineStructuralFunction({name:'advance',parameters:['n','a'],datatype:'Naturals',decreasingParameter:0,equations:[
  {patterns:[ctor('zero'),bind('a')],body:v('a')},
  {patterns:[ctor('succ',bind('n')),bind('a')],body:app('advance',v('n'),app('succ',v('a')))},
]});
const hugeA=BigInt('9'.repeat(120)), hugeB=BigInt('1234567890'.repeat(10));
let factorial=1n;for(let n=2n;n<=100n;n++)factorial*=n;
const examples:[string,ReturnType<typeof app>,ReturnType<typeof app>|ReturnType<typeof nat>,string[]][]=[
 ['advance',app('advance',nat(120),nat(3)),nat(123),['advance']],
 ['huge',app('times',nat(hugeA),nat(hugeB)),nat(hugeA*hugeB),['plus','times']],
 ['factorial',app('factorial',nat(100)),nat(factorial),['factorial','plus','times']],
 ['shifted',app('shiftedProduct',nat(3),nat(5)),nat(18),['plus','shiftedProduct']],
 ['stack',app('stack',nat(3)),app('pair',app('empty'),app('pair',app('empty'),app('pair',app('empty'),app('empty')))),['stack']],
];
for(const [name,left,right,deps]of examples)source.addTheorem(`fixture.${name}`,eq(left,right),compute(left,right,deps));
save('Admissions.g17c',compileSeparateKernelModule(base,base,source,checkpoint,{module:'Fixture.Admissions'}));
save('Computation.g17env',exportKernelEnvironment(source));
for(const [name]of examples)writeFileSync(join(output,`${name}.g17m`),encodeProofMachineBinary(compileProofMachine(exportTheorem(source,`fixture.${name}`))));

for(const [name]of examples){
  const program=structuredClone(compileProofMachine(exportTheorem(source,`fixture.${name}`)));
  const conclusion=program.formulas[program.code[program.root][1]];
  const number=name==='shifted'?'15':name==='huge'?String(hugeA*hugeB+1n):name==='factorial'?String(factorial+1n):'0';
  let symbol=program.symbols.indexOf(number);
  if(symbol<0){symbol=program.symbols.length;(program.symbols as string[]).push(number);}
  let term=program.terms.findIndex(row=>row[0]===3&&row[1]===symbol);
  if(term<0){term=program.terms.length;(program.terms as number[][]).push([3,symbol]);}
  const claim=program.formulas.length;
  (program.formulas as number[][]).push([1,conclusion[1],term]);
  (program.code[program.root] as number[])[1]=claim;
  writeFileSync(join(output,`${name}-incorrect.g17m`),encodeProofMachineBinary(program));
}

// Unit-level extension test: these two true lemmas are assumed in
// this isolated fixture. They are never added to a G17C foundation or Cumulus.
const unit=constructFoundation('ZFG');
const unitAxioms=[
 ['unit.emptyWellFounded',pred('wellFoundedOn',app('empty'),app('omega'))],
 ['unit.zeroInOmega',forall('x',pred('in',app('zero'),app('omega')))],
] as const;
for(const [n,f]of unitAxioms)unit.addAxiom(n,f);
const unitCheckpoint=unit.admissionCheckpoint();
unit.defineWellFoundedFunction({name:'wfConstant',parameters:['x'],coverageDatatype:'Naturals',coverageParameter:0,
 relation:app('empty'),domain:app('omega'),measure:app('zero'),wellFounded:axiom('unit.emptyWellFounded'),
 measureInDomain:axiom('unit.zeroInOmega'),decreases:[],equations:[
  {patterns:[ctor('zero')],body:app('zero')},{patterns:[ctor('succ',bind('n'))],body:app('zero')},
 ]});
const unitModule=compileKernelModule(unit,unitCheckpoint,{module:'Unit.WellFounded'});
save('unit-admission.json',{axioms:unitAxioms,events:unitModule.events,environment:unit.digest()});
console.log(`OCaml fixtures written to ${output}`);
