// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { installLibrarySearch } from '../workbench/library-search-ui.js';
class Element extends EventTarget {
  children: Element[] = []; textContent = ''; value = ''; open = false; focused = false;
  append(...children: Element[]) { this.children.push(...children); }
  replaceChildren() { this.children = []; }
  setAttribute() {}
  focus() { this.focused = true; }
  select() {}
  showModal() { this.open = true; }
  close() { this.open = false; this.dispatchEvent(new Event('close')); }
  querySelector() { return this.children[0]?.children[0]; }
}
class Worker extends EventTarget {
  static latest: Worker; requests: any[] = []; terminated = false;
  constructor() { super(); Worker.latest = this; }
  postMessage(data: any) { this.requests.push(data); }
  terminate() { this.terminated = true; }
  answer(data: any) { this.dispatchEvent(new MessageEvent('message', {data})); }
}
test('search dialog synchronizes files, ignores stale replies and navigates selected sources', () => {
  const elements = new Map(['librarySearchDialog','librarySearchInput','librarySearchStatus','librarySearchResults','librarySearch','closeLibrarySearch'].map(id => ['#'+id, new Element()]));
  const document = Object.assign(new EventTarget(), {
    querySelector: (selector: string) => selector === 'dialog[open]' ? [...elements.values()].find(e => e.open) : elements.get(selector),
    createElement: () => new Element(),
  });
  const oldDocument = globalThis.document, oldWorker = globalThis.Worker;
  Object.assign(globalThis, {document, Worker});
  let focused = 0, selected;
  try {
    installLibrarySearch({getFiles:()=>[{name:'User.g17',source:'module User'}], navigate: hit=>{selected=hit;}, focusEditor:()=>focused++});
    elements.get('#librarySearch')!.dispatchEvent(new Event('click'));
    const worker = Worker.latest, first = worker.requests[0];
    assert.deepEqual(first.files, [{name:'User.g17',source:'module User'}]);
    const input = elements.get('#librarySearchInput')!;
    input.value = 'name:root'; input.dispatchEvent(new Event('input'));
    worker.answer({id:first.id,result:{total:1,indexed:1,milliseconds:0,results:[]}});
    assert.equal(elements.get('#librarySearchStatus')!.textContent, 'Searching…');
    input.dispatchEvent(Object.assign(new Event('keydown'), {key:'Enter'}));
    const latest = worker.requests.at(-1);
    assert.equal(latest.files, undefined); assert.equal(latest.query, 'name:root');
    const hit = {name:'User.root',kind:'theorem',module:'User',file:'User.g17',line:4,signature:'theorem root'};
    worker.answer({id:latest.id,result:{total:1,indexed:1,milliseconds:1,results:[hit]}});
    elements.get('#librarySearchResults')!.children[0].children[0].dispatchEvent(new Event('click'));
    assert.deepEqual(selected, hit); assert.equal(elements.get('#librarySearchDialog')!.open, false); assert.equal(focused, 1);
    elements.get('#librarySearch')!.dispatchEvent(new Event('click'));
    assert.ok(worker.requests.at(-1).files);
    worker.dispatchEvent(new Event('error')); assert.equal(worker.terminated, true);
    elements.get('#closeLibrarySearch')!.dispatchEvent(new Event('click'));
    elements.get('#librarySearch')!.dispatchEvent(new Event('click'));
    assert.notEqual(Worker.latest, worker);
    elements.get('#closeLibrarySearch')!.dispatchEvent(new Event('click'));
  } finally { Object.assign(globalThis, {document:oldDocument, Worker:oldWorker}); }
});
