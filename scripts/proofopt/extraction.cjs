'use strict';
function extractionEngine(){
 const need=(x,m)=>{if(!x)throw Error(m)},roots=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"],safe=n=>typeof n==="string"&&/^[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*$/.test(n),cmp=(a,b)=>a<b?-1:a>b?1:0;
 // Only bounded, non-ubiquitous proof-value references provide pair evidence.
 // Index buckets are discarded entirely on overflow, independent of input order.
 function select(rows,limit=32,cap=24){
  need(Number.isInteger(limit)&&limit>0&&Number.isInteger(cap)&&cap>=2,"invalid budgets");
  const owners=new Map(),index=new Map();
  for(const row of rows){
   if(!row.project||row.kind!=="thm"||roots.includes(row.name)||!safe(row.name))continue;
   need(!owners.has(row.name)&&typeof row.module==="string"&&Array.isArray(row.value),"bad owner");
   const refs=new Set(row.value);owners.set(row.name,{module:row.module,refs});
   for(const ref of refs){
    if(!index.has(ref))index.set(ref,[]);
    const bucket=index.get(ref);if(bucket===null)continue;
    if(bucket.length===cap)index.set(ref,null);else bucket.push(row.name);
   }
  }
  const pairs=new Map();let contributions=0,usable=0;
  for(const bucket of index.values()){
   if(!bucket||bucket.length<2)continue;
   usable++;bucket.sort(cmp);
   for(let i=0;i<bucket.length;i++)for(let j=i+1;j<bucket.length;j++){
    const a=bucket[i],b=bucket[j],x=owners.get(a),y=owners.get(b);
    if(x.refs.has(b)||y.refs.has(a))continue;
    const key=a+"\t"+b;
    if(!pairs.has(key))pairs.set(key,{left:a,right:b,left_module:x.module,right_module:y.module,shared:0,score:0});
    const p=pairs.get(key);p.shared++;p.score+=Math.floor(1000/bucket.length);contributions++;
   }
  }
  const ranked=[...pairs.values()].filter(p=>p.shared>=2).sort((a,b)=>b.score-a.score||b.shared-a.shared||cmp(a.left,b.left)||cmp(a.right,b.right));
  // Reserve half the budget for cross-module pairs, then fill without duplicates.
  const selected=ranked.filter(p=>p.left_module!==p.right_module).slice(0,Math.floor(limit/2)),seen=new Set(selected);
  for(const p of ranked)if(selected.length<limit&&!seen.has(p)){selected.push(p);seen.add(p)}
  return {owners:owners.size,reference_buckets:index.size,usable_buckets:usable,contributions,eligible_pairs:ranked.length,pairs:selected.map((p,index)=>({index,...p}))};
 }
 function certificate(p,c){
  need(c.index===p.index&&c.left===p.left&&c.right===p.right,"pair mismatch");
  need(["pass","reject","inconclusive"].includes(c.outcome),"bad outcome");
  if(c.outcome!=="pass"){need(c.payload===null,"unexpected payload");return null}
  const x=c.payload;
  need(x&&["lemmaRefs","leftRefs","rightRefs"].every(k=>Array.isArray(x[k])&&x[k].every(v=>typeof v==="string"&&v.length)),"bad certificate");
  need(!x.lemmaRefs.includes("$lemma")&&x.leftRefs.includes("$lemma")&&x.rightRefs.includes("$lemma"),"missing helper reference");
  need(!x.lemmaRefs.includes(p.left)&&!x.lemmaRefs.includes(p.right),"helper references owner");
  return x;
 }
 function evaluate(g,p,x){
  const l=g.ids.get(p.left),r=g.ids.get(p.right),gates=new Map(g.gates.map(z=>[z.id,z.gate]));
  if(l===r||!gates.has(l)||!gates.has(r))return {status:"noneditable-owner"};
  const h=g.adj.length, lg=gates.get(l),rg=gates.get(r);
  const ids=rs=>[...new Set(rs.map(n=>n==="$lemma"?h:g.ids.get(n)))];
  const lm=ids(x.lemmaRefs),lv=ids(x.leftRefs),rv=ids(x.rightRefs);
  if([...lm,...lv,...rv].some(i=>i===undefined))return {status:"outside-exported-scope"};
  const patch=new Map([[lg,lv],[rg,rv],[h,lm]]),edges=(u,patched)=>patched?(patch.get(u)??g.adj[u]):g.adj[u];
  function reach(start,patched,cycle=false){
   const seen=new Uint8Array(h+1),q=cycle?[...edges(start,patched)]:[start];let weight=0;
   for(let i=0;i<q.length;i++){
    const u=q[i];if(cycle&&u===start)return {cycle:true};
    if(seen[u])continue;seen[u]=1;weight+=u===h?1:g.weights[u];
    for(const v of edges(u,patched))if(!seen[v])q.push(v);
   }
   return {seen,weight,cycle:false};
  }
  // Any new directed cycle contains one of the modified gates or the helper.
  if([lg,rg,h].some(i=>reach(i,true,true).cycle))return {status:"cycle"};
  const before=reach(g.superRoot,false),after=reach(g.superRoot,true);
  const per_root=[];
  for(let i=0;i<g.rootIds.length;i++){
   const a=reach(g.rootIds[i],false),b=reach(g.rootIds[i],true);
   for(let j=0;j<g.n;j++)if(b.seen[j]&&!a.seen[j])return {status:"existing-closure-expands"};
   per_root.push({name:g.roots[i],before:a.weight,after:b.weight,net:a.weight-b.weight});
  }
  return {status:"modeled",before:before.weight,after:after.weight,net:before.weight-after.weight,helper_counted:Number(after.seen[h]),per_root};
 }
 function selfTest(){
  let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"assert "+n+" "+JSON.stringify([a,b]));n++},fail=f=>{let yes=false;try{f()}catch{yes=true}eq(yes,true)};
  const row=(name,refs,module="M")=>({name,module,project:true,kind:"thm",value:refs});
  const sample=[row("A",["p","q","q"]),row("B",["p","q"],"N"),row("C",["p","q","A"]),row("D",["p","r"]),row("E",["p","r"]),row("riemannHypothesis",["p","q"])];
  const z=select(sample,10,4);eq(z.owners,5);eq(z.pairs.length,0); // p overflow, q alone insufficient
  const s=select(sample,10,10);eq(s.pairs.map(p=>[p.left,p.right]),[["A","B"],["B","C"],["D","E"]]);eq(select([...sample].reverse(),10,10),s);
  fail(()=>select([sample[0],sample[0]]));fail(()=>select(sample,0));
  let seed=77;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed>>>8};
  for(let t=0;t<240;t++){
   const rows=Array.from({length:3+rnd()%10},(_,i)=>row("N"+i,Array.from({length:7},(_,j)=>"c"+j).filter(()=>rnd()%3!==0),"M"+i%3)),cap=2+rnd()%10;
   const a=select(rows,1000,cap),expected=[];
   const counts=new Map();for(const x of rows)for(const c of x.value)counts.set(c,(counts.get(c)||0)+1);
   for(let i=0;i<rows.length;i++)for(let j=i+1;j<rows.length;j++){
    const x=rows[i],y=rows[j],shared=x.value.filter(c=>y.value.includes(c)&&counts.get(c)<=cap);
    if(shared.length>=2)expected.push([...[x.name,y.name].sort(cmp),shared.length,shared.reduce((k,c)=>k+Math.floor(1000/counts.get(c)),0)]);
   }
   const key=a=>JSON.stringify(a);eq(a.pairs.map(p=>[p.left,p.right,p.shared,p.score]).sort((a,b)=>cmp(key(a),key(b))),expected.sort((a,b)=>cmp(key(a),key(b))));
   eq(select([...rows].reverse(),1000,cap),a);
  }
  const g={ids:new Map(["R","A","B","X","Y","Z"].map((n,i)=>[n,i])),n:6,adj:[[1,2],[7],[8],[],[],[],[0],[3,4],[3,5]],weights:[0,1,1,1,1,1,0,0,0],gates:[{id:1,gate:7},{id:2,gate:8}],superRoot:6,rootIds:[0],roots:["R"]};
  const p={index:0,left:"A",right:"B"},x={lemmaRefs:["X"],leftRefs:["$lemma"],rightRefs:["$lemma"]};
  eq(certificate(p,{...p,outcome:"pass",payload:x}),x);
  eq(evaluate(g,p,x).net,1);eq(evaluate(g,p,x).helper_counted,1);
  eq(evaluate(g,p,{...x,lemmaRefs:["X","Y","Z"]}).net,-1);
  eq(evaluate(g,p,{...x,lemmaRefs:["A"]}).status,"cycle");
  eq(evaluate(g,p,{...x,lemmaRefs:["missing"]}).status,"outside-exported-scope");
  fail(()=>certificate(p,{...p,outcome:"pass",payload:{...x,rightRefs:[]}}));
  fail(()=>certificate(p,{...p,index:1,outcome:"pass",payload:x}));
  fail(()=>certificate(p,{...p,outcome:"reject",payload:x}));
  for(let t=0;t<512;t++){
   const refs=()=>["X","Y","Z"].filter(()=>rnd()%2===0),lm=refs(),lv=refs(),rv=refs(),v={lemmaRefs:lm,leftRefs:["$lemma",...lv],rightRefs:["$lemma",...rv]};
   const oracle=5-(3+new Set([...lm,...lv,...rv]).size);
   eq(evaluate(g,p,v).net,oracle);
  }
  return n;
 }
 return {need,roots,select,certificate,evaluate,selfTest};
}
module.exports=extractionEngine();
async function cli(){
 const a=module.exports,fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto"),zlib=require("node:zlib"),readline=require("node:readline");
 const [mode,file,sha,dir,input,output]=process.argv.slice(2),read=p=>JSON.parse(fs.readFileSync(p,"utf8")),write=(p,v)=>fs.writeFileSync(p,JSON.stringify(v,null,2)+"\n");
 if(mode==="--self-test"){console.log("PASS "+a.selfTest()+" assertions");return}
 a.need(mode==="select"||mode==="replay","mode");
 const s=read(path.join(dir,"scope.json")),raw=fs.readFileSync(path.join(dir,"scope.tsv"),"utf8");
 a.need(s.input_sha256===sha&&s.scope_sha256===crypto.createHash("sha256").update(raw).digest("hex"),"scope digest");
 const scope=new Map(raw.trimEnd().split("\n").map(line=>{const [name,m,p]=line.split("\t");return [name,{mask:Number(m),project:p==="1"}]}));
 a.need(scope.size===s.union_all&&JSON.stringify(s.root_names)===JSON.stringify(a.roots),"scope size/roots");
 const h=crypto.createHash("sha256"),stream=fs.createReadStream(file).pipe(zlib.createGunzip());stream.on("data",x=>h.update(x));
 let header=null,count=0,rows=[];
 const graph=mode==="replay"?require("./value_cut.cjs").graph(scope,s.root_names):null;
 for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
  const x=JSON.parse(line);
  if(!header){header=x;a.need(x.record==="header"&&x.schema===1&&x.measurement==="kernel-reference-graph"&&JSON.stringify(x.roots)===JSON.stringify(s.root_names),"header");continue}
  count++;if(graph)graph.add(x);else if(scope.get(x.name)?.project&&x.kind==="thm")rows.push({name:x.name,module:x.module,project:x.project,kind:x.kind,value:x.value});
 }
 a.need(h.digest("hex")===sha&&count===s.declarations,"graph mismatch");
 if(mode==="select"){
  const result={schema:1,input_sha256:sha,scope_sha256:s.scope_sha256,...a.select(rows)};
  write(input,result);console.log(JSON.stringify(result));return;
 }
 const report=read(input),cert=read(output),g=graph.finish();
 a.need(report.schema===1&&cert.schema===1&&report.input_sha256===sha&&cert.input_sha256===sha&&report.scope_sha256===s.scope_sha256&&cert.scope_sha256===s.scope_sha256&&report.pairs.length===cert.results.length,"certificate provenance");
 const reach=require("./parametric.cjs").reach;
 a.need(reach(g,g.superRoot,new Map()).weight===s.union_project_excluding_roots,"baseline mismatch");
 const results=report.pairs.map((p,i)=>{const x=a.certificate(p,cert.results[i]);return {...p,outcome:cert.results[i].outcome,model:x?a.evaluate(g,p,x):null}});
 const out={schema:1,measurement:"independent-kernel-certified-extraction-counterfactual-not-source-rewrite",input_sha256:sha,scope_sha256:s.scope_sha256,attempted:results.length,passed:results.filter(x=>x.outcome==="pass").length,results,actual_dependency_reduction:null,actual_dag_reduction:null,actual_cpu_reduction:null};
 write(process.argv[8],out);console.log(JSON.stringify(out));
}
if(require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
