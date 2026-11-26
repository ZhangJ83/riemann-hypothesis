import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {makeCore} from "./snapshot.mjs";
const core=makeCore(), s=JSON.parse(readFileSync(new URL("readable_snapshot.json",import.meta.url),"utf8"));
const clone=()=>structuredClone(s);
assert.equal(s.roots.length,5);
assert.ok(s.modules.length>=500);
assert.deepEqual(core.check(s,clone()).changed,[]);
for(const mutate of [x=>x.protectedFiles[0][1]="0".repeat(40),x=>x.dependencies.TauCeti="0".repeat(40),x=>x.roots.pop(),x=>x.modules[0].sha="0".repeat(40)]){
 const x=clone();mutate(x);assert.throws(()=>core.check(s,x));
}
const x=clone();const p=x.modules.find(m=>!s.protectedFiles.some(r=>r[0]===m.path));p.sha="0".repeat(40);assert.deepEqual(core.check(s,x,[p.path]).changed,[p.path]);
assert.throws(()=>core.check(s,s,["src/Fake.lean"]));
assert.equal(core.cacheDecision(0),"exact");assert.equal(core.cacheDecision(4),"baseline");
for(const c of [1,3,127])assert.throws(()=>core.cacheDecision(c));
assert.equal(core.parseTree("100644 blob "+"a".repeat(40)+"\tsrc/A B.lean\0")[0].path,"src/A B.lean");
console.log("snapshot regression tests passed");
