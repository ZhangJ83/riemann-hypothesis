'use strict';
function engine(){
 const need=(b,m)=>{if(!b)throw Error(m)},safe=n=>typeof n==="string"&&/^[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*$/.test(n);
 function parse(report,log){
  const outcomes=new Map();
  for(const line of log.split(/\r?\n/)){
   const m=line.match(/PROOFOPT_PARAM_(PASS|REJECT) (\d+)(?:\s|:|$)(.*)$/);if(!m)continue;
   const i=Number(m[2]);need(i<report.candidates.length&&!outcomes.has(i),"unexpected/duplicate outcome");
   const c=report.candidates[i];need(c.index===i,"bad candidate index");
   const refs=m[1]==="PASS"?JSON.parse(m[3].trim()):null;
   need(refs===null&&m[1]==="REJECT"||Array.isArray(refs)&&refs.every(x=>typeof x==="string")&&refs.includes(c.target),"invalid certificate references");
   outcomes.set(i,{index:i,source:c.source,target:c.target,refs:refs===null?null:[...new Set(refs)].sort()});
  }
  need(outcomes.size===report.candidates.length,"missing outcomes");
  return {schema:1,input_sha256:report.input_sha256,scope_sha256:report.scope_sha256,results:report.candidates.map((_,i)=>outcomes.get(i))};
 }
 function render(report,lean){
  return "import Main\n"+lean+"\n"+report.candidates.map((c,i)=>{
   need(c.index===i&&safe(c.source)&&safe(c.target),"bad candidate");return '#proofopt_param '+i+' '+JSON.stringify(c.source)+' '+JSON.stringify(c.target);
  }).join("\n")+"\n";
 }
 function reach(g,start,patch){
  const seen=new Uint8Array(g.adj.length),q=[start];seen[start]=1;let weight=0;
  for(let i=0;i<q.length;i++){const u=q[i];weight+=g.weights[u];for(const v of patch.get(u)??g.adj[u])if(!seen[v]){seen[v]=1;q.push(v)}}
  return {seen,weight};
 }
 // Every reference must occur in the owner's original closure and must
 // not reach the owner. Conservative bounded traversal fails closed.
 function guard(g,owner,refs,cap=24000000){
  let left=cap;
  function scan(start,stop){
   const seen=new Uint8Array(g.adj.length),q=[start];seen[start]=1;
   for(let i=0;i<q.length;i++){
    const u=q[i];if(u===stop)return {cycle:true};
    for(const v of g.adj[u]){if(--left<0)return {budget:true};if(!seen[v]){seen[v]=1;q.push(v)}}
   }return {seen};
  }
  const own=scan(owner,-1);if(own.budget)return "budget";
  for(const v of refs){if(!own.seen[v])return "outside-owner-closure";const t=scan(v,owner);if(t.cycle)return "cycle";if(t.budget)return "budget"}
  return "safe";
 }
 function replay(g,report,cert,opt={}){
  need(cert.schema===1&&cert.input_sha256===report.input_sha256&&cert.scope_sha256===report.scope_sha256,"provenance mismatch");
  need(cert.results.length===report.candidates.length,"candidate count mismatch");
  const gates=new Map(g.gates.map(x=>[x.id,x.gate])),base=reach(g,g.superRoot,new Map()),pool=[],rejected={};
  const reject=k=>{rejected[k]=(rejected[k]??0)+1};
  for(let i=0;i<cert.results.length;i++){
   const c=cert.results[i],expected=report.candidates[i];need(c.index===i&&c.source===expected.source&&c.target===expected.target,"candidate mismatch");
   if(c.refs===null){reject("kernel-reject");continue}
   need(Array.isArray(c.refs)&&c.refs.includes(c.target),"missing target");
   const owner=g.ids.get(c.source),gate=gates.get(owner),ids=c.refs.map(n=>g.ids.get(n));
   if(gate===undefined||ids.some(x=>x===undefined)){reject("missing-graph-reference");continue}
   const status=guard(g,owner,ids,opt.edgeBudget);if(status!=="safe"){reject(status);continue}
   const individual=base.weight-reach(g,g.superRoot,new Map([[gate,ids]])).weight;
   if(individual<=0){reject("nonpositive");continue}
   pool.push({...c,gate,ids,individual});
  }
  pool.sort((a,b)=>b.individual-a.individual||a.index-b.index);
  const patch=new Map(),chosen=[];let total=base.weight;
  for(const c of pool){if(patch.has(c.gate)){reject("duplicate-owner");continue}
   patch.set(c.gate,c.ids);const trial=reach(g,g.superRoot,patch).weight;
   if(trial>=total){patch.delete(c.gate);reject("nonpositive-marginal");continue}
   chosen.push({index:c.index,source:c.source,target:c.target,refs:c.refs,individual:c.individual,marginal:total-trial});total=trial;
  }
  const per_root=g.rootIds.map((id,i)=>{const a=reach(g,id,new Map()),b=reach(g,id,patch);for(let j=0;j<g.n;j++)need(!b.seen[j]||a.seen[j],"closure expanded");return {name:g.roots[i],before:a.weight,after:b.weight,net:a.weight-b.weight}});
  return {schema:1,measurement:"kernel-certified-parametric-counterfactual-not-source-rewrite",input_sha256:report.input_sha256,scope_sha256:report.scope_sha256,attempted:cert.results.length,kernel_pass:cert.results.filter(x=>x.refs!==null).length,rejected,before:base.weight,after:total,net:base.weight-total,chosen,per_root,actual_dependency_reduction:null,actual_dag_reduction:null,actual_cpu_reduction:null};
 }
 function selfTest(){
  let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"assertion "+n+" "+JSON.stringify([a,b]));n++};
  const fail=f=>{let yes=false;try{f()}catch{yes=true}eq(yes,true)};
  const report={input_sha256:"a",scope_sha256:"b",candidates:[{index:0,source:"A",target:"B"},{index:1,source:"C",target:"D"}]};
  const cert=parse(report,'info: PROOFOPT_PARAM_PASS 0 ["B","T","B"]\nPROOFOPT_PARAM_REJECT 1: no');
  eq(cert.results[0].refs,["B","T"]);eq(cert.results[1].refs,null);eq(render(report,"import Lean").includes('#proofopt_param 1 "C" "D"'),true);
  fail(()=>parse(report,""));fail(()=>parse(report,'PROOFOPT_PARAM_PASS 0 ["B"]\nPROOFOPT_PARAM_PASS 0 ["B"]'));fail(()=>parse(report,'PROOFOPT_PARAM_PASS 0 ["T"]'));
  const g={n:7,ids:new Map(["R","A","B","C","D","T","X"].map((x,i)=>[x,i])),adj:[[1,3],[8],[],[9],[],[],[],[0],[2,5,6],[4,6]],weights:[0,1,1,1,1,1,1,0,0,0],gates:[{id:1,gate:8},{id:3,gate:9}],superRoot:7,rootIds:[0],roots:["R"]};
  eq(guard(g,1,[2,5]),"safe");eq(guard(g,1,[4]),"outside-owner-closure");eq(guard(g,1,[1]),"cycle");eq(guard(g,1,[2],0),"budget");
  eq(replay(g,report,cert).net,0);
  const both=parse(report,'PROOFOPT_PARAM_PASS 0 ["B"]\nPROOFOPT_PARAM_PASS 1 ["D"]');
  eq(replay(g,report,both).net,1); // shared X not removed: zero individual gain omitted
  fail(()=>replay(g,report,{...both,input_sha256:"x"}));
  let seed=951;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed};
  for(let t=0;t<256;t++){
   const k=3+rnd()%8,adj=Array.from({length:k},(_,i)=>Array.from({length:k-i-1},(_,j)=>i+j+1).filter(()=>rnd()%3===0)),weights=adj.map(()=>rnd()%2),x={adj,weights};
   for(let i=0;i<k;i++){
    const p=new Map([[i,adj[i].filter(()=>rnd()%2===0)]]),s=new Set([0]);let prev=-1;
    while(prev!==s.size){prev=s.size;for(const u of s)for(const v of p.get(u)??adj[u])s.add(v)}
    const a=reach(x,0,p);eq(a.weight,[...s].reduce((v,u)=>v+weights[u],0));eq([...a.seen],adj.map((_,j)=>Number(s.has(j))));
   }
  }return n;
 }
 return {parse,render,replay,selfTest,reach,guard};
}
module.exports=engine();

async function cli(){
 const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto"),readline=require("node:readline"),a=module.exports;
 const args=process.argv.slice(2),read=p=>JSON.parse(fs.readFileSync(p,"utf8")),write=(p,x)=>fs.writeFileSync(p,JSON.stringify(x,null,2)+"\n");
 if(args[0]==="--self-test"){console.log("PASS "+a.selfTest()+" assertions");return}
 if(args[0]==="--render"){fs.writeFileSync(args[3],a.render(read(args[1]),fs.readFileSync(args[2],"utf8")));return}
 if(args[0]==="--parse"){write(args[3],a.parse(read(args[1]),fs.readFileSync(args[2],"utf8")));return}
 if(args.length!==6)throw Error("usage: parametric.cjs GRAPH SHA SCOPE_DIR REPORT CERT OUTPUT");
 const [file,sha,dir,r,c,out]=args,s=read(path.join(dir,"scope.json")),raw=fs.readFileSync(path.join(dir,"scope.tsv"),"utf8"),report=read(r),cert=read(c);
 if(s.input_sha256!==sha||s.scope_sha256!==crypto.createHash("sha256").update(raw).digest("hex")||report.input_sha256!==sha||report.scope_sha256!==s.scope_sha256)throw Error("graph/scope provenance mismatch");
 const scope=new Map();for(const line of raw.trimEnd().split("\n")){const [n,m,v]=line.split("\t");if(scope.has(n)||!["0","1"].includes(v))throw Error("bad scope");scope.set(n,{project:v==="1",mask:Number(m)})}
 const b=require("./value_cut.cjs").graph(scope,s.root_names),h=crypto.createHash("sha256"),stream=fs.createReadStream(file).pipe(zlib.createGunzip());stream.on("data",x=>h.update(x));let header=null,rows=0;
 for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){const x=JSON.parse(line);if(!header){header=x;if(x.record!=="header"||x.schema!==1||x.measurement!=="kernel-reference-graph"||JSON.stringify(x.roots)!==JSON.stringify(s.root_names))throw Error("bad header")}else{b.add(x);rows++}}
 if(h.digest("hex")!==sha||rows!==s.declarations||scope.size!==s.union_all)throw Error("graph mismatch");
 const g=b.finish();for(let i=0;i<g.rootIds.length;i++){const v=a.reach(g,g.rootIds[i],new Map());for(let j=0;j<g.n;j++)if(Boolean(v.seen[j])!==Boolean(scope.get(g.names[j]).mask&(1<<i)))throw Error("scope mask mismatch")}
 const result=a.replay(g,report,cert);if(result.before!==s.union_project_excluding_roots)throw Error("baseline mismatch");write(out,result);console.log(JSON.stringify(result));
}
if(require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
