// Exact-type, monomorphic theorem alias substitution. Simulations, not Lean proofs.
// All structural measurements use the existing structural-v1 interner.
import {lib} from "./export_metrics.mjs";
const check=(x,m)=>{if(!x)throw Error(m)};
const name=x=>Array.isArray(x)?lib.key(x):lib.key(x.split("."));
const order=(a,b)=>a<b?-1:a>b?1:0;
const eligible=d=>d.kind==="thm"&&!d.unsafe&&d.params.length===0&&d.value.length===1&&d.rules.length===0;
const metrics=(s,ks,own)=>lib.closure(s,ks,own);
const vector=m=>[m.project??m.total,m.total,m.dag.combined,m.dag.value];
const noWorse=(a,b)=>a.every((v,i)=>v<=b[i]);
function compareVector(a,b){for(let i=0;i<a.length;i++)if(a[i]!==b[i])return a[i]-b[i];return 0}
function validClosure(c){return !c.unexpected_axioms.length&&!c.unsafe.length}
function safeRelative(before,after){
 return validClosure(after)&&after.axioms.every(x=>before.axioms.includes(x));
}
function discover(s,roots,own=null){
 const ks=roots.map(name),base=metrics(s,ks,own),rootSet=new Set(ks),groups=new Map();
 if(own)for(const k of s.decls.keys())check(typeof own.get(k)==="boolean","incomplete ownership: "+k);
 for(const [k,d] of s.decls)if(eligible(d)){
  check(d.name===k,"declaration key mismatch");
  if(!groups.has(d.type))groups.set(d.type,[]);
  groups.get(d.type).push(k);
 }
 const result=[];
 for(const members of groups.values()){
  members.sort(order);
  for(const source of members){
   if(rootSet.has(source)||!base.live.has(source)||(own&&!own.get(source)))continue;
   const old=s.decls.get(source);
   for(const target of members){
    if(source===target)continue;
    const id=s.shared.expr(["const",target,[]],[],[target]);
    if(old.value[0]===id)continue;
    result.push({source,target,expectedType:old.type,expectedValue:old.value[0],replacement:id});
   }
  }
 }
 result.sort((a,b)=>order(a.source,b.source)||order(a.target,b.target));
 return result;
}
// All replacements retain the source declaration/type and change only its proof value.
// No arbitrary expression substitution; polymorphic and non-theorem declarations excluded.
function apply(s,roots,edits,own=null){
 const ks=roots.map(name),rootSet=new Set(ks),d=new Map(s.decls),used=new Set();
 for(const e of edits){
  const a=s.decls.get(e.source),b=s.decls.get(e.target);
  check(a&&b&&eligible(a)&&eligible(b),"noneligible theorem");
  check(!rootSet.has(e.source)&&(!own||own.get(e.source)===true),"protected source");
  check(e.source!==e.target&&!used.has(e.source),"self/conflicting alias");
  check(a.type===b.type&&a.type===e.expectedType&&a.value[0]===e.expectedValue,"stale or unequal type");
  const v=s.shared.expr(["const",e.target,[]],[],[e.target]);
  check(v===e.replacement,"replacement mismatch");
  used.add(e.source);d.set(e.source,{...a,value:[v]});
 }
 const candidate={...s,decls:d};
 // Reject cycles even in edited declarations that become unreachable from the roots.
 for(const e of edits)check(!metrics(candidate,[e.target],own).live.has(e.source),"alias cycle");
 return candidate;
}
// Exact search with a hard bound: refuse before enumeration rather than advertise partial results.
// Objective: project count, all declarations, combined DAG, value DAG (lexicographic).
// Require no regression in any of the four union metrics and no new axioms per root.
function solve(s,roots,{own=null,budget=2,maxStates=100000}={}){
 check(Number.isSafeInteger(budget)&&budget>=0,"invalid budget");
 check(Number.isSafeInteger(maxStates)&&maxStates>=1,"invalid state bound");
 const ks=roots.map(name),base=metrics(s,ks,own),per=ks.map(k=>metrics(s,[k],own));
 check(validClosure(base),"unsafe baseline");
 const candidates=discover(s,roots,own),group=new Map();
 for(const c of candidates){if(!group.has(c.source))group.set(c.source,[]);group.get(c.source).push(c)}
 const groups=[...group.values()],b=Math.min(budget,groups.length),counts=Array(b+1).fill(0n);counts[0]=1n;
 for(const g of groups)for(let j=b;j>0;j--)counts[j]+=counts[j-1]*BigInt(g.length);
 const expected=counts.reduce((a,v)=>a+v,0n);
 check(expected<=BigInt(maxStates),"state bound exceeded: "+expected);
 let best=[],bestV=vector(base),visited=0,rejected=0,feasible=0;
 const baseV=vector(base);
 function score(edits){
  visited++;
  let t;
  try{t=apply(s,roots,edits,own)}catch(e){if(e.message==="alias cycle"){rejected++;return}throw e}
  const m=metrics(t,ks,own),v=vector(m);
  if(!noWorse(v,baseV)||!safeRelative(base,m)||ks.some((k,i)=>!safeRelative(per[i],metrics(t,[k],own)))){rejected++;return}
  feasible++;
  if(compareVector(v,bestV)<0||(compareVector(v,bestV)===0&&edits.length<best.length)){
   best=edits.slice();bestV=v;
  }
 }
 // Enumerate only nonempty choices recursively; depth <= budget, not number of groups.
 // The explicit stack prevents overflow even when budget is large.
 const stack=[{start:0,edits:[]}];
 while(stack.length){
  const {start,edits}=stack.pop();score(edits);
  if(edits.length===b)continue;
  for(let i=groups.length-1;i>=start;i--)for(let j=groups[i].length-1;j>=0;j--)
   stack.push({start:i+1,edits:[...edits,groups[i][j]]});
 }
 check(BigInt(visited)===expected,"enumeration mismatch");
 const chosen=apply(s,roots,best,own),comparison=lib.compare(s,chosen,roots,own,own);
 check(comparison.structural_guard_passed,"final structural guard failed");
 return {schema:1,mode:"simulated exact-type theorem alias",kernel_verified:false,ownership:own?"explicit":"unavailable",
  candidate_count:candidates.length,source_count:groups.length,state_count:visited,feasible,rejected,
  budget,objective:["project_or_total","all_declarations","combined_dag","value_dag"],before:baseV,after:bestV,
  selected:best.map(e=>({source:JSON.parse(e.source),target:JSON.parse(e.target)})),
  per_root:comparison.per_root,union:comparison.union,
  caution:"Simulated proof values, not re-elaborated Lean source. Exact only within enumerated candidate class and budget."};
}
export {discover,apply,solve};
