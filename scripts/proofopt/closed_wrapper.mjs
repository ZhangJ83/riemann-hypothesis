// Closed unused-prefix theorem wrapper inlining, structural-v1 simulation only.
import {lib} from "./export_metrics.mjs";
function makeEngine(lib){
 const check=(x,m)=>{if(!x)throw Error(m)};
 const key=x=>Array.isArray(x)?lib.key(x):lib.key(x.split("."));
 function pool(){
  const p=lib.pool(),data=[],expr=p.expr;
  p.expr=(shape,children=[],deps=[])=>{const id=expr(shape,children,deps);if(data[id]===undefined)data[id]=shape;return id};
  p.shape=data;return p;
 }
 const eligible=d=>d.kind==="thm"&&!d.unsafe&&d.params.length===0&&d.value.length===1&&!d.rules.length;
 function shapes(s){
  check(Array.isArray(s.shared.shape)&&s.shared.shape.length===s.shared.es.length,"use capture pool for parsing");
  return s.shared.shape;
 }
 // loose(e) = 1 + maximum free de Bruijn index, or 0 for a closed expression.
 // The pool allocates children before parents; fail closed if this invariant breaks.
 function freeIndices(s){
  const ds=shapes(s),out=[];
  for(let i=0;i<ds.length;i++){
   const a=ds[i],cs=s.shared.es[i].children;
   check(cs.every(c=>Number.isSafeInteger(c)&&c>=0&&c<i),"non-topological expression");
   const f=j=>out[cs[j]];
   if(a[0]==="bvar")out.push(a[1]+1);
   else if(a[0]==="lam"||a[0]==="forallE")out.push(Math.max(f(0),Math.max(0,f(1)-1)));
   else if(a[0]==="letE")out.push(Math.max(f(0),f(1),Math.max(0,f(2)-1)));
   else out.push(cs.reduce((m,c)=>Math.max(m,out[c]),0));
  }
  return out;
 }
 function wrappers(s,own=null){
  const ds=shapes(s),loose=freeIndices(s),out=new Map();
  for(const [k,d] of s.decls){
   if(!eligible(d)||(own&&own.get(k)!==true))continue;
   let t=d.type,v=d.value[0],n=0;
   while(ds[t][0]==="forallE"&&ds[v][0]==="lam"){
    const a=ds[t],b=ds[v];
    // Exact domain and binder-info alignment, no defeq assumption.
    if(a[1]!==b[1]||a[2]!==b[2])break;
    t=a[3];v=b[3];n++;
    if(loose[t]===0&&loose[v]===0){
     out.set(k,{name:k,arity:n,body:v,result:t,expectedType:d.type,expectedValue:d.value[0]});break;
    }
   }
  }
  return out;
 }
 // Iterative DAG transformation. Applications of selected wrapper constants are
 // replaced only after the entire certified-unused prefix has been supplied.
 // Reusing a closed body under arbitrary surrounding binders needs no index shift.
 function rewrite(s,roots,selected,own=null){
  const ds=shapes(s),p=s.shared,limit=ds.length,ks=roots.map(key),protectedNames=new Set(ks);
  const base=lib.closure(s,ks,own),known=wrappers(s,own),chosen=new Map();
  for(const k of selected){check(known.has(k)&&!chosen.has(k),"unknown/duplicate wrapper");chosen.set(k,known.get(k))}
  const memo=new Map(),matches=new Map();
  function transform(root){
   const stack=[[root,false]];
   while(stack.length){
    const [id,ready]=stack.pop();if(memo.has(id))continue;
    check(id<limit,"unexpected original expression");
    const a=ds[id],e=p.es[id],cs=e.children;
    if(!ready){stack.push([id,true]);for(let j=cs.length-1;j>=0;j--)if(!memo.has(cs[j]))stack.push([cs[j],false]);continue}
    const kids=cs.map(c=>memo.get(c));let result=id,hit=null;
    if(a[0]==="app"){
     // Match original spine, not one manufactured by an earlier replacement.
     let cursor=id,argc=0;
     while(ds[cursor][0]==="app"&&argc<=maxArity){cursor=ds[cursor][1];argc++}
     const f=ds[cursor],rule=f[0]==="const"&&f[2].length===0?chosen.get(f[1]):null;
     if(rule&&argc===rule.arity){result=rule.body;hit=rule.name;}
    }
    if(hit){matches.set(id,hit)}
    else if(kids.some((c,j)=>c!==cs[j])){
     let b;
     switch(a[0]){
      case "app":b=["app",...kids];break;
      case "lam":case "forallE":b=[a[0],a[1],...kids];break;
      case "letE":b=["letE",...kids];break;
      case "proj":b=["proj",a[1],a[2],...kids];break;
      default:throw Error("unsupported child-bearing expression "+a[0]);
     }
     result=p.expr(b,kids,e.deps);
    }
    memo.set(id,result);
   }
   return memo.get(root);
  }
  const maxArity=Math.max(0,...Array.from(chosen.values(),x=>x.arity));
  const decls=new Map(s.decls),changed=[];
  for(const k of [...base.live].sort()){
   const d=s.decls.get(k);
   if(!eligible(d)||protectedNames.has(k)||(own&&own.get(k)!==true))continue;
   const v=transform(d.value[0]);
   if(v!==d.value[0]){decls.set(k,{...d,value:[v]});changed.push(k)}
  }
  return {state:{...s,decls},changed,matchedNodes:matches.size,matchedWrappers:[...new Set(matches.values())].sort()};
 }
 function solve(s,roots,{own=null,budget=2,maxStates=4096}={}){
  check(Number.isSafeInteger(budget)&&budget>=0&&Number.isSafeInteger(maxStates)&&maxStates>=1,"invalid limits");
  const ks=roots.map(key),base=lib.closure(s,ks,own);
  if(own)for(const k of s.decls.keys())check(typeof own.get(k)==="boolean","missing ownership");
  check(!base.unexpected_axioms.length&&!base.unsafe.length,"unsafe baseline");
  const all=[...wrappers(s,own).keys()].sort();
  // Drop rules that have no matching use in the editable reachable proofs.
  const active=all.filter(k=>rewrite(s,roots,[k],own).changed.length);
  const b=Math.min(budget,active.length);
  let count=1n,term=1n;
  for(let i=1;i<=b;i++){term=term*BigInt(active.length-i+1)/BigInt(i);count+=term}
  check(count<=BigInt(maxStates),"state bound exceeded: "+count);
  const vec=m=>[m.project??m.total,m.total,m.dag.combined,m.dag.value];
  const before=vec(base),cmp=(a,b)=>{for(let i=0;i<a.length;i++)if(a[i]!==b[i])return a[i]-b[i];return 0};
  let best=before,bestSet=[],visited=0,feasible=0,bestChanged=[];
  const stack=[[0,[]]];
  while(stack.length){
   const [start,sel]=stack.pop();visited++;
   const r=rewrite(s,roots,sel,own),m=lib.closure(r.state,ks,own),v=vec(m);
   const guard=lib.compare(s,r.state,roots,own,own);
   // All root closures must be subsets of the respective original closures,
   // not just have equal cardinality. This blocks hidden dependency relocation.
   const subset=ks.every(k=>{const x=lib.closure(s,[k],own).live;return [...lib.closure(r.state,[k],own).live].every(y=>x.has(y))});
   if(guard.structural_guard_passed&&subset&&v.every((x,i)=>x<=before[i])){
    feasible++;
    if(cmp(v,best)<0||(cmp(v,best)===0&&sel.length<bestSet.length)){best=v;bestSet=sel;bestChanged=r.changed}
   }
   if(sel.length<b)for(let i=active.length-1;i>=start;i--)stack.push([i+1,[...sel,active[i]]]);
  }
  check(BigInt(visited)===count,"enumeration mismatch");
  const final=rewrite(s,roots,bestSet,own);
  return {schema:1,mode:"closed-prefix wrapper inlining simulation",kernel_verified:false,ownership:own?"explicit":"unavailable",wrappers:all.length,active:active.length,states:visited,feasible,before,after:best,selected:bestSet.map(JSON.parse),changed:bestChanged.map(JSON.parse),matched_dag_nodes:final.matchedNodes,comparison:lib.compare(s,final.state,roots,own,own)};
 }
 return {pool,freeIndices,wrappers,rewrite,solve};
}
export const engine=makeEngine(lib);
