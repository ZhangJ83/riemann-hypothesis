'use strict';
function clusterEngine(){
 const need=(x,m)=>{if(!x)throw Error(m)},cmp=(a,b)=>a<b?-1:a>b?1:0, roots=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"],safe=n=>typeof n==="string"&&/^[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*$/.test(n);
 function select(rows,{limit=48,cap=12,seeds=4096}={}){
  need([limit,cap,seeds].every(Number.isSafeInteger)&&limit>0&&cap>=3&&cap<=24&&seeds>0,"bad budgets");
  const owners=new Map(),index=new Map();
  for(const r of rows){
   if(!r.project||r.kind!=="thm"||roots.includes(r.name)||!safe(r.name))continue;
   need(!owners.has(r.name)&&typeof r.module==="string"&&Array.isArray(r.value)&&r.value.every(x=>typeof x==="string"),"invalid owner");
   const refs=new Set(r.value);owners.set(r.name,{module:r.module,refs});
   for(const x of refs){if(!index.has(x))index.set(x,[]);const b=index.get(x);if(b!==null){if(b.length===cap)index.set(x,null);else b.push(r.name)}}
  }
  const pairMap=new Map();let usable=0,pairContributions=0;
  for(const b of index.values()){
   if(!b||b.length<3)continue;usable++;b.sort(cmp);
   for(let i=0;i<b.length;i++)for(let j=i+1;j<b.length;j++){
    const a=b[i],c=b[j];if(owners.get(a).refs.has(c)||owners.get(c).refs.has(a))continue;
    const key=a+"\t"+c, p=pairMap.get(key)||{a,b:c,shared:0,score:0};p.shared++;p.score+=Math.floor(1000/b.length);pairMap.set(key,p);pairContributions++;
   }
  }
  const ranked=[...pairMap.values()].filter(p=>p.shared>=2).sort((a,b)=>b.score-a.score||b.shared-a.shared||cmp(a.a,b.a)||cmp(a.b,b.b));
  const cross=p=>owners.get(p.a).module!==owners.get(p.b).module;
  const seedList=ranked.filter(cross).slice(0,Math.floor(seeds/2)), seedSet=new Set(seedList);
  for(const p of ranked)if(seedList.length<seeds&&!seedSet.has(p)){seedList.push(p);seedSet.add(p)}
  const triples=new Map();
  for(const p of seedList){
   const a=owners.get(p.a),b=owners.get(p.b),common=[...a.refs].filter(x=>b.refs.has(x)&&index.get(x)?.length>=3);
   const third=new Map();
   for(const ref of common)for(const c of index.get(ref))if(c!==p.a&&c!==p.b){const o=third.get(c)||{shared:0,score:0};o.shared++;o.score+=Math.floor(1000/index.get(ref).length);third.set(c,o)}
   for(const [c,stat] of third){
    if(stat.shared<2)continue;
    const d=owners.get(c);if(a.refs.has(c)||b.refs.has(c)||d.refs.has(p.a)||d.refs.has(p.b))continue;
    const ns=[p.a,p.b,c].sort(cmp), key=ns.join("\t"),modules=ns.map(n=>owners.get(n).module);
    const v={owners:ns,modules,shared:stat.shared,score:stat.score,module_count:new Set(modules).size};
    if(triples.has(key))need(JSON.stringify(triples.get(key))===JSON.stringify(v),"non-invariant score");else triples.set(key,v);
   }
  }
  const all=[...triples.values()].sort((a,b)=>b.score-a.score||b.shared-a.shared||b.module_count-a.module_count||cmp(a.owners.join("\t"),b.owners.join("\t")));
  const chosen=all.filter(x=>x.module_count>1).slice(0,Math.floor(limit/2)),seen=new Set(chosen);
  for(const x of all)if(chosen.length<limit&&!seen.has(x)){chosen.push(x);seen.add(x)}
  return {owners:owners.size,reference_buckets:index.size,usable_buckets:usable,pair_contributions:pairContributions,eligible_pair_seeds:ranked.length,used_pair_seeds:seedList.length,seed_budget_truncated:ranked.length>seedList.length,eligible_triples:all.length,clusters:chosen.map((x,index)=>({index,...x}))};
 }
 function validate(p,c){
  need(c.index===p.index&&JSON.stringify(c.owners)===JSON.stringify(p.owners),"cluster mismatch");
  need(p.owners.length===3&&new Set(p.owners).size===3&&p.owners.every(safe),"bad owners");
  need(["pass","reject","inconclusive"].includes(c.outcome),"bad status");
  if(c.outcome!=="pass"){need(c.payload===null,"nonpass payload");return null}
  const x=c.payload, refs=a=>Array.isArray(a)&&a.every(v=>typeof v==="string"&&v.length);
  need(x&&x.ownerCount===3&&refs(x.lemmaRefs)&&Array.isArray(x.ownerRefs)&&x.ownerRefs.length===3&&x.ownerRefs.every(a=>refs(a)&&a.includes("$lemma")),"bad refs");
  need(!x.lemmaRefs.includes("$lemma")&&!p.owners.some(n=>x.lemmaRefs.includes(n)),"helper owner reference");
  for(const k of ["holeCount","scopeArity","usedScopeArity"])need(Number.isSafeInteger(x[k])&&x[k]>=0,"invalid "+k);
  need(x.holeCount<=4&&x.usedScopeArity<=x.scopeArity,"invalid arity");
  for(const k of ["localRawDagBefore","localRawDagAfter"])need(x[k]===null||Number.isSafeInteger(x[k])&&x[k]>0&&x[k]<=200000,"bad local count");
  return x;
 }
 function evaluate(g,p,x){
  const gates=new Map(g.gates.map(z=>[z.id,z.gate])),h=g.adj.length, os=p.owners.map(n=>g.ids.get(n));
  if(os.some(i=>!gates.has(i))||new Set(os).size!==3)return {status:"noneditable-owner"};
  const ids=rs=>[...new Set(rs.map(n=>n==="$lemma"?h:g.ids.get(n)))],patch=new Map([[h,ids(x.lemmaRefs)]]);
  for(let j=0;j<3;j++)patch.set(gates.get(os[j]),ids(x.ownerRefs[j]));
  if([...patch.values()].some(a=>a.some(i=>i===undefined)))return {status:"outside-exported-scope"};
  const edges=(u,modified)=>modified?(patch.get(u)??g.adj[u]):g.adj[u];
  function reach(start,modified,cycle=false){
   const seen=new Uint8Array(h+1),q=[];let weight=0,cyclic=false;
   const add=u=>{if(cycle&&u===start){cyclic=true;return}if(!seen[u]){seen[u]=1;q.push(u)}};
   if(cycle)for(const v of edges(start,modified))add(v);else add(start);
   for(let i=0;i<q.length&&!cyclic;i++){const u=q[i];weight+=u===h?1:g.weights[u];for(const v of edges(u,modified))add(v)}
   return {seen,weight,cyclic};
  }
  if([...patch.keys()].some(u=>reach(u,true,true).cyclic))return {status:"cycle"};
  const a=reach(g.superRoot,false),b=reach(g.superRoot,true),per_root=[];
  for(let i=0;i<g.rootIds.length;i++){
   const u=reach(g.rootIds[i],false),v=reach(g.rootIds[i],true);
   for(let j=0;j<g.n;j++)if(v.seen[j]&&!u.seen[j])return {status:"existing-closure-expands"};
   per_root.push({name:g.roots[i],before:u.weight,after:v.weight,net:u.weight-v.weight});
  }
  return {status:"modeled",before:a.weight,after:b.weight,net:a.weight-b.weight,helper_counted:Number(b.seen[h]),per_root};
 }
 function selfTest(){
  let assertions=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"assert "+assertions+" "+JSON.stringify([a,b]));assertions++},fail=f=>{let yes=false;try{f()}catch{yes=true}eq(yes,true)};
  const row=(name,value,module="M")=>({name,module,project:true,kind:"thm",value});
  const sample=[row("A",["p","q","q"]),row("B",["p","q"],"N"),row("C",["p","q"],"P"),row("D",["p","r"]),row("riemannHypothesis",["p","q"])];
  eq(select(sample,{limit:10,cap:4}).clusters.map(x=>x.owners),[["A","B","C"]]);eq(select(sample,{limit:10,cap:3}).clusters,[]);eq(select([...sample].reverse(),{limit:10,cap:4}),select(sample,{limit:10,cap:4}));
  fail(()=>select([sample[0],sample[0]]));fail(()=>select(sample,{cap:2}));
  let seed=123456;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed>>>8};
  for(let t=0;t<400;t++){
   const rows=Array.from({length:3+rnd()%8},(_,i)=>row("N"+i,Array.from({length:8},(_,j)=>"c"+j).filter(()=>rnd()%3!==0),"M"+i%3)),cap=3+rnd()%9;
   const counts=new Map();for(const x of rows)for(const c of x.value)counts.set(c,(counts.get(c)||0)+1);
   const expected=[];
   for(let i=0;i<rows.length;i++)for(let j=i+1;j<rows.length;j++)for(let k=j+1;k<rows.length;k++){
    const [a,b,c]=[rows[i],rows[j],rows[k]],shared=a.value.filter(r=>b.value.includes(r)&&c.value.includes(r)&&counts.get(r)<=cap);
    if(shared.length>=2)expected.push([[a.name,b.name,c.name].sort(cmp),shared.length,shared.reduce((n,r)=>n+Math.floor(1000/counts.get(r)),0)]);
   }
   const v=select(rows,{limit:1000,cap,seeds:1000}), key=a=>JSON.stringify(a), sort=a=>a.sort((x,y)=>cmp(key(x),key(y)));
   eq(sort(v.clusters.map(x=>[x.owners,x.shared,x.score])),sort(expected));eq(select([...rows].reverse(),{limit:1000,cap,seeds:1000}),v);
  }
  const names=["R","A","B","C","X","Y","Z"],g={ids:new Map(names.map((n,i)=>[n,i])),n:7,adj:[[1,2,3],[8],[9],[10],[],[],[],[0],[4,5],[4,6],[5,6]],weights:[0,1,1,1,1,1,1,0,0,0,0],gates:[{id:1,gate:8},{id:2,gate:9},{id:3,gate:10}],superRoot:7,rootIds:[0],roots:["R"]};
  const p={index:0,owners:["A","B","C"]},x={lemmaRefs:["X"],ownerRefs:[["$lemma"],["$lemma"],["$lemma"]],ownerCount:3,holeCount:2,scopeArity:4,usedScopeArity:0,localRawDagBefore:10,localRawDagAfter:8};
  eq(validate(p,{...p,outcome:"pass",payload:x}),x);eq(evaluate(g,p,x).net,1);eq(evaluate(g,p,{...x,lemmaRefs:["X","Y","Z"]}).net,-1);eq(evaluate(g,p,{...x,lemmaRefs:["A"]}).status,"cycle");eq(evaluate(g,p,{...x,lemmaRefs:["missing"]}).status,"outside-exported-scope");
  fail(()=>validate(p,{...p,outcome:"pass",payload:{...x,usedScopeArity:5}}));fail(()=>validate(p,{...p,outcome:"pass",payload:{...x,ownerRefs:[["$lemma"],["$lemma"],[]]}}));fail(()=>validate(p,{...p,outcome:"reject",payload:x}));
  for(let t=0;t<768;t++){
   const refs=()=>["X","Y","Z"].filter(()=>rnd()%2===0),lm=refs(),r=Array.from({length:3},()=>refs()),v={...x,lemmaRefs:lm,ownerRefs:r.map(a=>["$lemma",...a])};
   eq(evaluate(g,p,v).net,6-(4+new Set([...lm,...r.flat()]).size));
  }
  // Per-root expansion must be rejected even if the union already contains X.
  const multi={...g,adj:[[1,2,3],[8],[9],[10],[],[],[],[0,4],[5],[5],[5]],rootIds:[0,4],roots:["R","X"]};
  eq(evaluate(multi,p,x).status,"existing-closure-expands");
  eq(select(sample,{limit:1,cap:4,seeds:1}).seed_budget_truncated,true);
  return assertions;
 }
 return {need,roots,select,validate,evaluate,selfTest};
}
module.exports=clusterEngine();

async function cli(){
 const a=module.exports,fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto"),zlib=require("node:zlib"),readline=require("node:readline");
 const [mode,file,sha,dir,input,certFile,output]=process.argv.slice(2),read=p=>JSON.parse(fs.readFileSync(p,"utf8")),write=(p,v)=>fs.writeFileSync(p,JSON.stringify(v,null,2)+"\n");
 if(mode==="--self-test"){console.log("PASS "+a.selfTest()+" assertions");return}
 a.need(mode==="select"||mode==="replay","mode");
 const s=read(path.join(dir,"scope.json")),raw=fs.readFileSync(path.join(dir,"scope.tsv"),"utf8");
 a.need(s.input_sha256===sha&&s.scope_sha256===crypto.createHash("sha256").update(raw).digest("hex"),"scope digest");
 const scope=new Map(raw.trimEnd().split("\n").map(line=>{const [name,m,p]=line.split("\t");return [name,{mask:Number(m),project:p==="1"}]}));
 a.need(scope.size===s.union_all&&JSON.stringify(s.root_names)===JSON.stringify(a.roots),"scope size/roots");
 const hash=crypto.createHash("sha256"),stream=fs.createReadStream(file).pipe(zlib.createGunzip());stream.on("data",x=>hash.update(x));
 let header=null,count=0,rows=[];
 const graph=mode==="replay"?require("./value_cut.cjs").graph(scope,s.root_names):null;
 for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
  const x=JSON.parse(line);
  if(!header){header=x;a.need(x.record==="header"&&x.schema===1&&x.measurement==="kernel-reference-graph"&&JSON.stringify(x.roots)===JSON.stringify(s.root_names),"header");continue}
  count++;if(graph)graph.add(x);else if(scope.get(x.name)?.project&&x.kind==="thm")rows.push({name:x.name,module:x.module,project:x.project,kind:x.kind,value:x.value});
 }
 a.need(hash.digest("hex")===sha&&count===s.declarations,"graph mismatch");
 if(mode==="select"){const result={schema:1,input_sha256:sha,scope_sha256:s.scope_sha256,...a.select(rows)};write(input,result);console.log(JSON.stringify(result));return}
 const report=read(input),cert=read(certFile),g=graph.finish();
 a.need(report.schema===1&&cert.schema===1&&report.input_sha256===sha&&cert.input_sha256===sha&&report.scope_sha256===s.scope_sha256&&cert.scope_sha256===s.scope_sha256&&report.clusters.length===cert.results.length,"certificate provenance");
 a.need(cert.selection_sha256===crypto.createHash("sha256").update(fs.readFileSync(input)).digest("hex"),"selection digest");
 a.need(require("./parametric.cjs").reach(g,g.superRoot,new Map()).weight===s.union_project_excluding_roots,"baseline mismatch");
 const results=report.clusters.map((p,i)=>{const x=a.validate(p,cert.results[i]),model=x?a.evaluate(g,p,x):null;return {...p,outcome:cert.results[i].outcome,model,local_raw_dag_delta:x&&x.localRawDagBefore!==null&&x.localRawDagAfter!==null?x.localRawDagBefore-x.localRawDagAfter:null,scope_arity:x?.scopeArity??null,used_scope_arity:x?.usedScopeArity??null}});
 const out={schema:1,measurement:"independent-kernel-certified-triple-extraction-counterfactual-not-source-rewrite",input_sha256:sha,scope_sha256:s.scope_sha256,attempted:results.length,passed:results.filter(x=>x.outcome==="pass").length,model_positive:results.filter(x=>x.model?.status==="modeled"&&x.model.net>0).length,nonregressing_model_positive_local:results.filter(x=>x.model?.status==="modeled"&&x.model.net>=0&&x.local_raw_dag_delta>0).length,results,actual_dependency_reduction:null,actual_dag_reduction:null,actual_cpu_reduction:null};
 write(output,out);console.log(JSON.stringify(out));
}
if(require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
