import {readFileSync} from "node:fs";
import {engine} from "./closed_wrapper.mjs";
import {lib} from "./export_metrics.mjs";
function test(engine,lib,realText){
 const results=[],check=(x,m)=>{if(!x)throw Error(m)},eq=(a,b)=>check(JSON.stringify(a)===JSON.stringify(b),JSON.stringify([a,b]));
 const run=(name,f)=>{f();results.push(name)};
 const p=engine.pool(),s=lib.parse(realText,p),k=x=>lib.key([x]),N=x=>p.expr(["const",k(x),[]],[],[k(x)]);
 const K=x=>p.expr(["const",lib.key(x.split(".")),[]],[],[lib.key(x.split("."))]);
 const app=(f,a)=>p.expr(["app",f,a],[f,a]),bv=i=>p.expr(["bvar",i]),bind=(tag,a,b)=>p.expr([tag,"default",a,b],[a,b]);
 const baseDecl=s.decls.get(lib.key(["Nat","add_succ"])),t=baseDecl.type,proof=K("Nat.add_succ"),dom=K("Nat"),arg=K("Nat.zero");
 const mk=(name,type,value)=>({name:k(name),kind:"thm",type,value:[value],params:[],rules:[],kernel:[],unsafe:false});
 function augmented(){
  const w=mk("wrap",bind("forallE",dom,t),bind("lam",dom,proof));
  const c=mk("caller",t,app(N("wrap"),arg));
  const r=mk("root",t,N("caller"));
  return {...s,decls:new Map([...s.decls,[w.name,w],[c.name,c],[r.name,r]])};
 }
 const a=augmented(),roots=["root"],own=new Map([...a.decls.keys()].map(x=>[x,true]));
 run("real export baseline",()=>eq(lib.closure(s,[lib.key(["Nat","add_succ"])]).dag.combined,337));
 run("closed wrapper discovered",()=>eq(engine.wrappers(a).get(k("wrap")).arity,1));
 run("closed body containing bound variables",()=>{const x=bind("lam",dom,bv(0));eq(engine.freeIndices(a)[x],0)});
 run("loose variable detected",()=>eq(engine.freeIndices(a)[bv(1)],2));
 run("dependent proof rejected",()=>{const w=mk("bad",bind("forallE",dom,t),bind("lam",dom,bv(0)));const q={...a,decls:new Map([...a.decls,[w.name,w]])};check(!engine.wrappers(q).has(w.name),"dependent wrapper")});
 run("dependent result rejected",()=>{const w=mk("bad",bind("forallE",dom,bv(0)),bind("lam",dom,proof));const q={...a,decls:new Map([...a.decls,[w.name,w]])};check(!engine.wrappers(q).has(w.name),"dependent result")});
 run("domain mismatch rejected",()=>{const w=mk("bad",bind("forallE",dom,t),bind("lam",t,proof));const q={...a,decls:new Map([...a.decls,[w.name,w]])};check(!engine.wrappers(q).has(w.name),"domain mismatch")});
 run("two unused binders",()=>{const w=mk("two",bind("forallE",dom,bind("forallE",dom,t)),bind("lam",dom,bind("lam",dom,proof)));const q={...a,decls:new Map([...a.decls,[w.name,w]])};eq(engine.wrappers(q).get(w.name).arity,1)});
 run("caller rewrite",()=>{const r=engine.rewrite(a,roots,[k("wrap")],own);eq(r.changed,[k("caller")]);eq(r.state.decls.get(k("caller")).value,[proof]);eq(a.decls.get(k("caller")).value,[app(N("wrap"),arg)])});
 run("root protected",()=>eq(engine.rewrite(a,["caller"],[k("wrap")],own).changed,[]));
 run("external callers protected",()=>{const o=new Map(own);o.set(k("caller"),false);eq(engine.rewrite(a,roots,[k("wrap")],o).changed,[])});
 run("external wrapper rejected",()=>{const o=new Map(own);o.set(k("wrap"),false);check(!engine.wrappers(a,o).has(k("wrap")),"external wrapper")});
 run("unapplied wrapper unchanged",()=>{const c=mk("caller",t,N("wrap"));const q={...a,decls:new Map(a.decls).set(c.name,c)};eq(engine.rewrite(q,roots,[k("wrap")]).changed,[])});
 run("overapplication rebuilt",()=>{const c=mk("caller",t,app(app(N("wrap"),arg),arg));const q={...a,decls:new Map(a.decls).set(c.name,c)};eq(engine.rewrite(q,roots,[k("wrap")]).state.decls.get(c.name).value,[app(proof,arg)])});
 run("under binder no capture",()=>{const c=mk("caller",t,bind("lam",dom,app(N("wrap"),bv(0))));const q={...a,decls:new Map(a.decls).set(c.name,c)};eq(engine.rewrite(q,roots,[k("wrap")]).state.decls.get(c.name).value,[bind("lam",dom,proof)])});
 run("duplicate rule rejected",()=>{let bad=false;try{engine.rewrite(a,roots,[k("wrap"),k("wrap")])}catch(e){bad=true}check(bad,"duplicate")});
 const real=engine.solve(s,["Nat.add_succ"],{budget:2});
 const aug=engine.solve(a,roots,{own,budget:2});
 run("real sample no metric regression",()=>check(real.after.every((x,i)=>x<=real.before[i]),"regression"));
 run("augmented closure compression",()=>{eq(aug.selected,[["wrap"]]);eq(aug.before[0]-aug.after[0],1);check(aug.comparison.structural_guard_passed,"guard")});
 run("zero budget",()=>eq(engine.solve(a,roots,{own,budget:0}).selected,[]));
 run("bounded search refuses excess",()=>{let bad=false;try{engine.solve(a,roots,{own,budget:2,maxStates:1})}catch(e){bad=e.message.includes("state bound")}check(bad,"limit")});
 return {results,real:{wrappers:real.wrappers,active:real.active,states:real.states,before:real.before,after:real.after,selected:real.selected},aug:{wrappers:aug.wrappers,active:aug.active,states:aug.states,before:aug.before,after:aug.after,selected:aug.selected,changed:aug.changed,matched:aug.matched_dag_nodes}};
}
const result=test(engine,lib,readFileSync(process.argv[2],"utf8"));
console.log(JSON.stringify(result,null,2));
