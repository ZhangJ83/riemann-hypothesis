import {readFileSync} from "node:fs";
import {lib} from "./export_metrics.mjs";
function tests(lib,realText){
 let passed=0;const names=[];
 const eq=(a,b)=>{if(JSON.stringify(a)!==JSON.stringify(b))throw Error(`expected ${JSON.stringify(b)}, got ${JSON.stringify(a)}`)},ok=x=>{if(!x)throw Error("assertion failed")},fail=(f,w)=>{let hit=false;try{f()}catch(e){hit=String(e).includes(w)}ok(hit)},test=(n,f)=>{f();passed++;names.push(n)};
 const M={meta:{lean:{githash:"fixture",version:"4.x"},exporter:{name:"fixture",version:"3.1.0"},format:{version:"3.1.0"}}},mk=rs=>[M,...rs].map(JSON.stringify).join("\n"),name=(i,s,pre=0)=>({in:i,str:{pre,str:s}}),th=(n,t,v)=>({thm:{name:n,levelParams:[],type:t,value:v,all:[n]}}),ax=(n,t)=>({axiom:{name:n,levelParams:[],type:t,isUnsafe:false}}),co=(i,n)=>({ie:i,const:{name:n,us:[]}}),binder=(i,n,t,b,tag="lam")=>({ie:i,[tag]:{name:n,type:t,body:b,binderInfo:"default"}});
 const base=[name(1,"R"),name(2,"A"),name(3,"B"),name(4,"x"),name(5,"y"),{ie:0,sort:0},{ie:1,bvar:0},binder(2,4,0,1),binder(3,5,0,1),co(4,2),co(5,3),th(2,0,2),th(3,0,3),th(1,0,4)];
 const own=lib.owners(["R","A","B"].map(n=>({name_parts:[n],project:true})));
 test("alpha-renamed binders interned",()=>{const s=lib.parse(mk(base));eq(s.decls.get(lib.key(["A"])).value,s.decls.get(lib.key(["B"])).value);eq(s.raw.expressions,6)});
 test("reachable DAG excludes dead declarations",()=>{const r=lib.report(lib.parse(mk(base)),["R"],own);eq(r.union.project,2);eq(r.union.total,2);eq(r.union.dag,{type:1,value:4,combined:4});eq(r.union.project_dag.combined,4)});
 test("missing ownership fails closed",()=>fail(()=>lib.report(lib.parse(mk(base)),["R"],lib.owners([{name_parts:["R"],project:true}])),"ownership missing"));
 test("unknown ownership is null not zero",()=>{const r=lib.report(lib.parse(mk(base)),["R"]);eq(r.union.project,null);eq(r.union.project_dag,null)});
 test("metadata erased without losing references",()=>{const b=[...base.slice(0,-1),{ie:6,mdata:{expr:4,data:{foo:1}}},th(1,0,6)];eq(lib.report(lib.parse(mk(b)),["R"]).union.dag.combined,4)});
 test("universe structure preserved",()=>{const s=lib.parse(mk([name(1,"R"),{il:1,succ:0},{ie:0,sort:0},{ie:1,sort:1},th(1,0,1)]));eq(lib.report(s,["R"]).union.dag.combined,2)});
 test("numeric and string name components distinct",()=>{const s=lib.parse(mk([name(1,"R"),name(2,"1",1),{in:3,num:{pre:1,i:1}},{ie:0,sort:0},th(2,0,0),th(3,0,0)]));eq(s.decls.size,2);ok(s.decls.has(lib.key(["R",1])))});
 test("duplicate index rejected",()=>fail(()=>lib.parse(mk([...base,{ie:0,sort:0}])),"duplicate expression"));
 test("unknown variant and missing indices rejected",()=>{fail(()=>lib.parse(mk([...base,{ie:9,foo:1}])),"unknown expression");fail(()=>lib.parse(mk([...base,{ie:9,app:{fn:0,arg:99}}])),"unresolved expression")});
 test("unknown format rejected",()=>fail(()=>lib.parse(JSON.stringify({meta:{...M.meta,format:{version:"9"}}})),"unsupported export format"));
 test("unresolved reachable constant rejected",()=>{const s=lib.parse(mk([name(1,"R"),name(2,"Missing"),{ie:0,sort:0},co(1,2),th(1,0,1)]));fail(()=>lib.report(s,["R"]),"unresolved reachable")});
 test("inductive metadata and recursor RHS retained",()=>{const s=lib.parse(mk([name(1,"R"),name(2,"I"),name(3,"C"),name(4,"rec"),name(5,"D"),{ie:0,sort:0},co(1,4),co(2,5),th(5,0,0),{inductive:{types:[{name:2,levelParams:[],type:0,all:[2],ctors:[3]}],ctors:[{name:3,levelParams:[],type:0,induct:2}],recs:[{name:4,levelParams:[],type:0,all:[2],rules:[{ctor:3,rhs:2}]}]}},th(1,0,1)]));eq(lib.report(s,["R"]).union.total,5);eq(lib.report(s,["R"]).union.dag.value,3)});
 test("literal implicit support retained",()=>{const s=lib.parse(mk([name(1,"R"),name(2,"Nat"),{ie:0,sort:0},{ie:1,natVal:"7"},th(2,0,0),th(1,0,1)]));eq(lib.report(s,["R"]).union.total,2)});
 test("per-root axiom growth not hidden in union",()=>{const p=lib.pool(),rs=[name(1,"R"),name(2,"S"),name(3,"propext"),{ie:0,sort:0},co(1,3),ax(3,0)],a=lib.parse(mk([...rs,th(1,0,0),th(2,0,1)]),p),b=lib.parse(mk([...rs,th(1,0,1),th(2,0,1)]),p),r=lib.compare(a,b,["R","S"]);eq(r.union.new_axioms,[]);eq(r.per_root[0].new_axioms,[lib.key(["propext"])]);eq(r.structural_guard_passed,false)});
 test("unexpected baseline axiom rejected",()=>{const p=lib.pool(),x=lib.parse(mk([name(1,"R"),name(2,"sorryAx"),{ie:0,sort:0},co(1,2),ax(2,0),th(1,0,1)]),p);eq(lib.compare(x,x,["R"]).structural_guard_passed,false)});
 test("root statement survives index renumbering",()=>{const p=lib.pool(),a=lib.parse(mk(base),p),b=lib.parse(mk([name(99,"R"),{ie:99,sort:0},th(99,99,99)]),p),r=lib.compare(a,b,["R"]);eq(r.root_types[0].same,true);eq(r.union.all_declarations.reduced,1);eq(r.kernel_verified,false)});
 test("changed root type and ownership drift rejected",()=>{const p=lib.pool(),a=lib.parse(mk(base),p),b=lib.parse(mk([...base.slice(0,-1),th(1,1,4)]),p);eq(lib.compare(a,b,["R"]).structural_guard_passed,false);const changed=lib.owners([{name_parts:["R"],project:false},{name_parts:["A"],project:true}]);eq(lib.compare(a,a,["R"],own,changed).structural_guard_passed,false)});
 test("graph adapter preserves dependency references",()=>{const s=lib.parse(mk(base)),g=lib.graph(s,["R"],own);eq(g.nodes.length,3);eq(g.nodes.find(n=>n.name===lib.key(["R"])).value,[lib.key(["A"])])});
 test("10000-deep DAG uses iterative traversal",()=>{const rs=[name(1,"R"),{ie:0,sort:0}];for(let i=1;i<=10000;i++)rs.push({ie:i,app:{fn:i-1,arg:i-1}});rs.push(th(1,0,10000));eq(lib.report(lib.parse(mk(rs)),["R"]).union.dag.combined,10001)});
 let actual=null;
 if(realText){
  test("published Nat.add_succ: independent raw reference oracle",()=>{
   const p=lib.pool(),s=lib.parse(realText,p),r=lib.report(s,["Nat.add_succ"]),rows=realText.trim().split(/\r?\n/).map(JSON.parse),nm=new Map([[0,[]]]),ex=new Map(),dc=new Map();
   for(const x of rows){if(x.in!==undefined){const a=x.str||x.num;nm.set(x.in,[...nm.get(a.pre),x.str?a.str:a.i])}if(x.ie!==undefined)ex.set(x.ie,x);for(const t of ["def","thm","opaque","axiom","quot"])if(x[t])for(const d of Array.isArray(x[t])?x[t]:[x[t]])dc.set(d.name,{...d,kind:t});if(x.inductive)for(const [f,t] of [["inductiveVals","ind"],["constructorVals","ctor"],["recursorVals","rec"]])for(const d of x.inductive[f])dc.set(d.name,{...d,kind:t})}
   const byName=new Map([...nm].map(([i,p])=>[JSON.stringify(p),i])),by=n=>byName.get(JSON.stringify(n.split("."))),visited=new Set(),seen=new Set(),stack=[by("Nat.add_succ")];
   while(stack.length){const n=stack.pop();if(visited.has(n))continue;visited.add(n);const d=dc.get(n);ok(d);stack.push(...(d.all||[]),...(d.ctors||[]));if(d.induct!==undefined)stack.push(d.induct);const pending=[d.type];if(d.value!==undefined)pending.push(d.value);for(const rule of d.rules||[]){stack.push(rule.ctor);pending.push(rule.rhs)}if(d.kind==="quot")stack.push(...["Quot","Quot.mk","Quot.lift","Quot.ind","Eq"].map(by));
    while(pending.length){const i=pending.pop();if(seen.has(i))continue;seen.add(i);const e=ex.get(i);ok(e);if(e.const)stack.push(e.const.name);if(e.proj){stack.push(e.proj.typeName);pending.push(e.proj.struct)}if(e.app)pending.push(e.app.fn,e.app.arg);for(const t of ["lam","forallE","letE"])if(e[t]){pending.push(e[t].type,e[t].body);if(t==="letE")pending.push(e[t].value)}if(e.mdata)pending.push(e.mdata.expr);if(e.natVal!==undefined)stack.push(by("Nat"));if(e.strVal!==undefined)stack.push(by("Char.ofNat"),by("String.ofList"))}
   }
   eq(r.union.total,visited.size);ok(r.union.dag.combined<=seen.size);eq(lib.compare(s,lib.parse(realText,p),["Nat.add_succ"]).union.dag.reduced,0);
   actual={raw:r.raw,reachable:r.union.total,raw_reachable_expression_ids:seen.size,normalized_dag:r.union.dag,axioms:r.union.axioms.map(lib.nameText),format:r.meta.format.version};
  });
  test("v3.1 schema migration of published fixture preserves metrics",()=>{
   const rs=realText.trim().split(/\r?\n/).map(JSON.parse),out=[];
   for(const x of rs){if(x.meta){out.push({meta:{...x.meta,format:{version:"3.1.0"}}});continue}if(x.inductive){out.push({inductive:{types:x.inductive.inductiveVals,ctors:x.inductive.constructorVals,recs:x.inductive.recursorVals}});continue}const t=["def","thm","opaque","axiom","quot"].find(t=>Array.isArray(x[t]));if(t){for(const d of x[t])out.push({[t]:d});continue}out.push(x)}
   const r=lib.report(lib.parse(out.map(JSON.stringify).join("\n")),["Nat.add_succ"]);eq(r.union.total,actual.reachable);eq(r.union.dag,actual.normalized_dag);
  });
 }
 return {passed,tests:names,real_sample:actual};
}
console.log(JSON.stringify(tests(lib,process.argv[2]?readFileSync(process.argv[2],"utf8"):null),null,2));
