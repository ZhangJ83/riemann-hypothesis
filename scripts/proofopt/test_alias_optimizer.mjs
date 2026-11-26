import {lib} from "./export_metrics.mjs";
import {discover,apply,solve} from "./alias_optimizer.mjs";
const K=x=>lib.key([x]);
function assert(x,m="assertion failed"){if(!x)throw Error(m)}
function throws(f,m){try{f()}catch(e){assert(e.message.includes(m),e.message);return}throw Error("expected "+m)}
function fixture(){
 const shared=lib.pool(),p=shared.expr(["sort",0]),decls=new Map();
 const c=x=>shared.expr(["const",K(x),[]],[],[K(x)]);
 const add=(n,v,type=p,kind="thm",params=[])=>decls.set(K(n),{name:K(n),kind,type,params,value:[v],rules:[],kernel:[],unsafe:false});
 // Distinct terms and theorem names; graph-only fixture, not a Lean proof.
 add("a",p);add("b",p);add("x",c("a"));add("y",c("x"));add("r",c("y"));
 const s={shared,decls,meta:{lean:{githash:"test",version:"test"},exporter:{name:"test",version:"test"},format:{version:"3.0.0"}},raw:{}};
 return {s,add,c,p,own:new Map([...decls.keys()].map(k=>[k,true]))};
}
function run(real){
 let passed=0;const test=(n,f)=>{f();passed++};
 test("exact budget improvement",()=>{const {s,own}=fixture(),r=solve(s,["r"],{own,budget:2});assert(r.before[0]===4&&r.after[0]===3);assert(r.selected.length===1);assert(!r.kernel_verified)});
 test("zero budget",()=>{const {s}=fixture(),r=solve(s,["r"],{budget:0});assert(r.state_count===1&&r.selected.length===0)});
 test("no root edits",()=>{const {s}=fixture();assert(discover(s,["r"]).every(x=>x.source!==K("r")))});
 test("cycle rejected",()=>{const {s}=fixture();const e=discover(s,["r"]).find(x=>x.source===K("x")&&x.target===K("y"));throws(()=>apply(s,["r"],[e]),"cycle")});
 test("stale rejected",()=>{const {s}=fixture(),e=discover(s,["r"])[0];throws(()=>apply(s,["r"],[{...e,expectedValue:-1}]),"stale")});
 test("conflict rejected",()=>{const {s}=fixture(),e=discover(s,["r"])[0];throws(()=>apply(s,["r"],[e,e]),"conflicting")});
 test("bound fails closed",()=>{const {s}=fixture();throws(()=>solve(s,["r"],{budget:2,maxStates:1}),"state bound")});
 test("incomplete ownership rejected",()=>{const {s,own}=fixture();own.delete(K("b"));throws(()=>discover(s,["r"],own),"incomplete")});
 test("external sources excluded",()=>{const {s,own}=fixture();own.set(K("y"),false);assert(discover(s,["r"],own).every(x=>x.source!==K("y")))});
 test("different types excluded",()=>{const {s,add,p}=fixture();add("other",p,s.shared.expr(["sort",9]));assert(discover(s,["r"]).every(x=>x.target!==K("other")))});
 test("polymorphic theorem excluded",()=>{const {s,add,p}=fixture();add("poly",p,p,"thm",["u"]);assert(discover(s,["r"]).every(x=>x.target!==K("poly")))});
 test("no baseline mutation",()=>{const {s}=fixture(),old=s.decls.get(K("y")).value[0];solve(s,["r"]);assert(s.decls.get(K("y")).value[0]===old)});
 test("new axiom rejected",()=>{const {s,add,c,p}=fixture();add("badAx",p,p,"axiom");add("bad",c("badAx"));const r=solve(s,["r"]);assert(r.selected.every(e=>e.target[0]!=="bad"));assert(r.rejected>0)});
 const s=lib.parse(real);
 const realReport=solve(s,["Nat.add_succ"],{budget:2});
 test("real export baseline",()=>{assert(realReport.before[1]===27&&realReport.before[2]===337);assert(realReport.selected.length===0)});
 // Extend a real export with hypothetical theorem aliases of exactly its exported type.
 // These extensions are in-memory simulations, not claims of additional real exported declarations.
 const root=lib.key(["Nat","add_succ"]),orig=s.decls.get(root),d=new Map(s.decls);
 const constOf=k=>s.shared.expr(["const",k,[]],[],[k]);
 const add=(n,v)=>d.set(K(n),{...orig,name:K(n),value:[v],kernel:[]});
 add("alias_a",orig.value[0]);add("alias_b",constOf(K("alias_a")));add("alias_root",constOf(K("alias_b")));
 const extended={...s,decls:d};
 const aug=solve(extended,[["Nat","add_succ"],"alias_root"],{budget:2});
 test("real-export-derived alias chain",()=>{assert(aug.before[1]===30&&aug.after[1]===29);assert(aug.selected.length===1);assert(aug.union.all_declarations.reduced===1)});
 // Independent brute force combination oracle (no optimizer search implementation).
 let seed=271828;
 const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 let cases=0;
 test("random exhaustive oracle",()=>{
  for(let j=0;j<100;j++){
   const {s,add,c,p}=fixture();
   for(let i=0;i<3;i++)add("extra"+i,rnd(2)?c(["a","b","x","y"][rnd(4)]):p);
   const es=discover(s,["r"]),baseline=lib.closure(s,[K("r")]),v=m=>[m.total,m.total,m.dag.combined,m.dag.value];
   const bv=v(baseline);let best=bv;
   const cmp=(a,b)=>{for(let i=0;i<a.length;i++)if(a[i]!==b[i])return a[i]-b[i];return 0};
   function trial(edits){
    let t;try{t=apply(s,["r"],edits)}catch(e){if(e.message==="alias cycle")return;throw e}
    const m=v(lib.closure(t,[K("r")]));
    if(m.every((x,i)=>x<=bv[i])&&cmp(m,best)<0)best=m;
   }
   trial([]);for(let i=0;i<es.length;i++){trial([es[i]]);for(let k=i+1;k<es.length;k++)if(es[i].source!==es[k].source)trial([es[i],es[k]])}
   const r=solve(s,["r"],{budget:2});assert(JSON.stringify(r.after)===JSON.stringify(best));cases++;
  }
 });
 return {passed,cases,realReport,aug};
}
export {run};
