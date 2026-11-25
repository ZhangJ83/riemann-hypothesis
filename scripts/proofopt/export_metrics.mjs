// ProofOpt export analysis, structural-v1. Not a kernel checker.
// Format: https://github.com/leanprover/lean4export/blob/df81913eee5519d5a88ae5b0fd701b5298cc29ab/format_ndjson.md
function library(){
const assert=(v,m)=>{if(!v)throw Error(m)}, nat=(x,l)=>{assert(Number.isSafeInteger(x)&&x>=0,`invalid ${l}`);return x}, arr=(x,l)=>{assert(Array.isArray(x),`expected array: ${l}`);return x}, obj=(x,l)=>{assert(x&&typeof x==="object"&&!Array.isArray(x),`expected object: ${l}`);return x}, str=(x,l)=>{assert(typeof x==="string",`invalid ${l}`);return x}, bool=(x,l)=>{assert(typeof x==="boolean",`invalid ${l}`);return x};
const key=parts=>JSON.stringify(arr(parts,"name parts").map(p=>typeof p==="string"?p:nat(p,"numeric name component"))), plain=s=>key(str(s,"root").split(".")), nameText=k=>JSON.parse(k).map(p=>typeof p==="number"?String(p):p.includes(".")?`«${p}»`:p).join(".");
const lookup=(m,i,l)=>{nat(i,l);assert(m.has(i),`unresolved ${l} ${i}`);return m.get(i)}, put=(m,i,v,l)=>{nat(i,l);assert(!m.has(i),`duplicate ${l} ${i}`);m.set(i,v)}, uniq=xs=>[...new Set(xs)];
const allow=new Set(["propext","Quot.sound","Classical.choice"].map(plain));
function pool(){
 const es=[],em=new Map(),ls=[],lm=new Map();
 function intern(table,items,data,record){const k=JSON.stringify(data);if(table.has(k))return table.get(k);const i=items.length;table.set(k,i);items.push(record);return i}
 return {es,ls,level:data=>intern(lm,ls,data,data),expr:(data,children=[],deps=[])=>intern(em,es,data,{children,deps})};
}
function parser(shared=pool()){
 let meta=null,lines=0;
 const names=new Map([[0,[]]]),levels=new Map([[0,shared.level(["zero"])]]),exprs=new Map(),decls=new Map();
 const N=i=>key(lookup(names,i,"name")),L=i=>lookup(levels,i,"level"),E=i=>lookup(exprs,i,"expression"),NL=(x,l)=>arr(x,l).map(N);
 const one=(r,skip)=>{const ks=Object.keys(r).filter(k=>k!==skip);assert(ks.length===1,`ambiguous record ${ks.join(",")}`);return ks[0]};
 const decl=(kind,d)=>{
  obj(d,kind);const k=N(d.name);assert(k!=="[]"&&!decls.has(k),`anonymous or duplicate declaration ${k}`);
  const type=E(d.type),params=NL(d.levelParams,"levelParams"),value=["thm","def","opaque"].includes(kind)?[E(d.value)]:[];
  let rules=[],kernel=[];
  if(["thm","def","opaque","ind","rec"].includes(kind))kernel.push(...NL(d.all,"all"));
  if(kind==="ind")kernel.push(...NL(d.ctors,"ctors"));
  if(kind==="ctor")kernel.push(N(d.induct));
  if(kind==="rec")for(const r of arr(d.rules,"recursor rules")){kernel.push(N(r.ctor));rules.push(E(r.rhs))}
  if(kind==="quot")kernel.push(...["Quot","Quot.mk","Quot.lift","Quot.ind","Eq"].map(plain));
  decls.set(k,{name:k,kind,type,params,value,rules,kernel:uniq(kernel.filter(x=>x!==k)),unsafe:d.isUnsafe===true||(kind==="def"&&d.safety!=="safe")});
 };
 function row(r){
  obj(r,"record");lines++;
  if(!meta){
   assert(lines===1&&Object.keys(r).length===1&&r.meta,"first record must be metadata");meta=obj(r.meta,"metadata");
   assert(["3.0.0","3.1.0"].includes(meta.format?.version),"unsupported export format");
   assert(typeof meta.lean?.githash==="string"&&meta.lean.githash&&typeof meta.lean?.version==="string","missing Lean identity");
   assert(typeof meta.exporter?.name==="string"&&typeof meta.exporter?.version==="string","missing exporter identity");return;
  }
  if(Object.hasOwn(r,"in")){
   const t=one(r,"in"),v=obj(r[t],"name"),pre=lookup(names,v.pre,"name prefix");
   assert(t==="str"||t==="num","unknown name variant");
   put(names,r.in,[...pre,t==="str"?str(v.str,"name string"):nat(v.i,"name number")],"name");return;
  }
  if(Object.hasOwn(r,"il")){
   const t=one(r,"il"),v=r[t];let data;
   if(t==="succ")data=[t,L(v)];else if(t==="param")data=[t,N(v)];
   else if(t==="max"||t==="imax"){assert(arr(v,t).length===2,"bad level arity");data=[t,...v.map(L)]}
   else throw Error(`unknown level variant ${t}`);
   put(levels,r.il,shared.level(data),"level");return;
  }
  if(Object.hasOwn(r,"ie")){
   const t=one(r,"ie"),v=r[t];let data,children=[],deps=[];
   switch(t){
    case "bvar":data=[t,nat(v,t)];break;
    case "sort":data=[t,L(v)];break;
    case "const":deps=[N(v.name)];data=[t,deps[0],arr(v.us,"universe arguments").map(L)];break;
    case "app":children=[E(v.fn),E(v.arg)];data=[t,...children];break;
    case "lam":case "forallE":N(v.name);assert(["default","implicit","strictImplicit","instImplicit"].includes(v.binderInfo),"invalid binder info");children=[E(v.type),E(v.body)];data=[t,v.binderInfo,...children];break;
    case "letE":N(v.name);bool(v.nondep,"nondep");children=[E(v.type),E(v.value),E(v.body)];data=[t,...children];break;
    case "proj":deps=[N(v.typeName)];children=[E(v.struct)];data=[t,deps[0],nat(v.idx,"projection index"),...children];break;
    case "natVal":assert(/^(0|[1-9]\d*)$/.test(str(v,t)),"invalid nat literal");data=[t,v];deps=[plain("Nat")];break;
    case "strVal":data=[t,str(v,t)];deps=["Char.ofNat","String.ofList"].map(plain);break;
    case "mdata":put(exprs,r.ie,E(v.expr),"expression");return;
    default:throw Error(`unknown expression variant ${t}`);
   }
   put(exprs,r.ie,shared.expr(data,children,deps),"expression");return;
  }
  const t=one(r,null),v=r[t];
  if(t==="inductive"){
   const fs=meta.format.version==="3.0.0"?["inductiveVals","constructorVals","recursorVals"]:["types","ctors","recs"];
   for(let i=0;i<3;i++)for(const d of arr(v[fs[i]],fs[i]))decl(["ind","ctor","rec"][i],d);
  }else if(["axiom","def","thm","opaque","quot"].includes(t)){
   const ds=Array.isArray(v)&&meta.format.version==="3.0.0"?v:[v];assert(ds.length>0,"empty declaration group");
   for(const d of ds)decl(t,d);
  }else throw Error(`unknown declaration variant ${t}`);
 }
 function line(s){assert(s.trim().length>0,"blank NDJSON record");try{row(JSON.parse(s))}catch(e){throw Error(`NDJSON line ${lines||1}: ${e.message}`)}}
 function finish(){assert(meta&&decls.size>0,"empty export");return {shared,meta,decls,raw:{lines,names:names.size-1,levels:levels.size-1,expressions:exprs.size,declarations:decls.size}}}
 return {row,line,finish};
}
function parse(text,shared=pool()){const p=parser(shared);for(const s of text.replace(/\r?\n$/,"").split(/\r?\n/))p.line(s);return p.finish()}
function owners(rows){const m=new Map();for(const r of arr(rows,"ownership rows")){const k=key(r.name_parts);assert(k!=="[]"&&typeof r.project==="boolean","invalid ownership");assert(!m.has(k),`duplicate ownership ${k}`);m.set(k,r.project)}return m}
function walkExpr(s,initial,seen=new Set(),onDep=()=>{}){
 const todo=[...initial];while(todo.length){const i=todo.pop();if(seen.has(i))continue;seen.add(i);const e=s.shared.es[i];assert(e,`unknown normalized expression ${i}`);for(const d of e.deps)onDep(d);for(const c of e.children)todo.push(c)}return seen;
}
function closure(s,roots,own=null){
 assert(roots.length>0&&new Set(roots).size===roots.length,"empty/duplicate roots");
 const todo=[...roots],live=new Set(),walked=new Set(),type=new Set(),value=new Set(),projectType=new Set(),projectValue=new Set(),add=d=>{if(!live.has(d))todo.push(d)};
 while(todo.length){const k=todo.pop();if(live.has(k))continue;const d=s.decls.get(k);assert(d,`unresolved reachable declaration ${k}`);live.add(k);
  if(own)assert(own.has(k),`ownership missing for ${k}`);
  for(const ref of d.kernel)add(ref);
  walkExpr(s,[d.type,...d.value,...d.rules],walked,add);walkExpr(s,[d.type],type);walkExpr(s,[...d.value,...d.rules],value);
  if(own?.get(k)){walkExpr(s,[d.type],projectType);walkExpr(s,[...d.value,...d.rules],projectValue)}
 }
 const union=(a,b)=>{let n=a.size;for(const x of b)if(!a.has(x))n++;return n}, list=f=>[...live].filter(k=>f(s.decls.get(k))).sort(),axioms=list(d=>d.kind==="axiom");
 return {live,total:live.size,project:own?[...live].filter(k=>own.get(k)).length:null,axioms,unexpected_axioms:axioms.filter(k=>!allow.has(k)),unsafe:list(d=>d.unsafe),dag:{type:type.size,value:value.size,combined:union(type,value)},project_dag:own?{type:projectType.size,value:projectValue.size,combined:union(projectType,projectValue)}:null};
}
function report(s,roots,own=null){
 const ks=roots.map(x=>Array.isArray(x)?key(x):plain(x)),clean=({live,...m})=>m;
 return {schema:1,normalization:"structural-v1",meta:s.meta,raw:s.raw,ownership:own?"explicit-manifest":"unavailable",roots:ks.map(k=>({name:JSON.parse(k),...clean(closure(s,[k],own))})),union:clean(closure(s,ks,own)),caveat:"Export reference closure, not a type checker. Kernel metadata and literal support retained. No definitional unfolding. Owner coverage required for project-only counts."};
}
function compare(a,b,roots,ownerA=null,ownerB=null){
 assert(a.shared===b.shared,"comparison requires one shared structural interner");
 assert(a.meta.lean.githash===b.meta.lean.githash&&a.meta.lean.version===b.meta.lean.version,"different Lean versions");
 assert(a.meta.format.version===b.meta.format.version&&a.meta.exporter.name===b.meta.exporter.name&&a.meta.exporter.version===b.meta.exporter.version,"different export format/exporter");
 assert(Boolean(ownerA)===Boolean(ownerB),"inconsistent ownership mode");
 const before=report(a,roots,ownerA),after=report(b,roots,ownerB);
 const rootTypes=roots.map(x=>{const k=Array.isArray(x)?key(x):plain(x),p=a.decls.get(k),q=b.decls.get(k);return {name:JSON.parse(k),same:p.kind===q.kind&&p.type===q.type&&JSON.stringify(p.params)===JSON.stringify(q.params)}});
 const delta=(x,y)=>x===null||y===null?null:{before:x,after:y,reduced:x-y,fraction:x?(x-y)/x:null};
 const diff=(x,y)=>({project:delta(x.project,y.project),all_declarations:delta(x.total,y.total),dag:delta(x.dag.combined,y.dag.combined),value_dag:delta(x.dag.value,y.dag.value),project_dag:delta(x.project_dag?.combined??null,y.project_dag?.combined??null),new_axioms:y.axioms.filter(k=>!x.axioms.includes(k)),unexpected_axioms:y.unexpected_axioms,unsafe:y.unsafe});
 const perRoot=before.roots.map((x,i)=>({name:x.name,...diff(x,after.roots[i])})),union=diff(before.union,after.union),consistentOwnership=ownerA?[...ownerA].every(([k,v])=>!ownerB.has(k)||ownerB.get(k)===v):null;
 return {before,after,root_types:rootTypes,consistentOwnership,per_root:perRoot,union,structural_guard_passed:rootTypes.every(r=>r.same)&&consistentOwnership!==false&&[...perRoot,union].every(r=>!r.new_axioms.length&&!r.unexpected_axioms.length&&!r.unsafe.length),kernel_verified:false};
}
function graph(s,roots,own){
 assert(own,"explicit ownership required for graph adapter");
 const refs=ids=>{const out=new Set();walkExpr(s,ids,new Set(),x=>out.add(x));return [...out].sort()},nodes=[];
 for(const [k,d] of s.decls){assert(own.has(k),`ownership missing for ${k}`);const type=refs([d.type]),value=refs(d.value),kernel=uniq([...d.kernel,...refs(d.rules)]).sort();
  for(const r of [...type,...value,...kernel])assert(s.decls.has(r),`unresolved graph reference ${r}`);
  nodes.push({name:k,display:nameText(k),kind:d.kind,project:own.get(k),module:"ownership-manifest",type,value,kernel});
 }
 const ks=roots.map(x=>Array.isArray(x)?key(x):plain(x));for(const k of ks)assert(s.decls.has(k),`missing root ${k}`);
 return {schema:1,measurement:"kernel-reference-graph",roots:ks,nodes};
}
return {pool,parser,parse,owners,closure,report,compare,graph,key,nameText};
}
export const lib=library();
