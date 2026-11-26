'use strict';
function engine(cut){
 const need=(x,m)=>{if(!x)throw Error(m)},safe=n=>typeof n==="string"&&/^[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*$/.test(n);
 function graph(scope,roots){
  const b=cut.graph(scope,roots),sig=new Map();
  return {add(r){b.add(r);if(scope.has(r.name)&&r.kind==="thm"&&safe(r.name))sig.set(r.name,JSON.stringify([...new Set(r.type)].sort()))},
   finish(){const g=b.finish();g.sig=g.names.map(n=>sig.get(n));g.gateOf=new Map(g.gates.map(c=>[c.id,c.gate]));return g}};
 }
 function intervals(d,n){
  const cs=Array.from({length:d.count+1},()=>[]);
  for(let i=2;i<=d.count;i++)cs[d.idom[i]].push(i);
  const lo=new Int32Array(n).fill(-1),hi=new Int32Array(n).fill(-1);
  let tick=0;const q=[[1,0]];lo[d.vertex[1]]=tick++;
  while(q.length){const a=q[q.length-1],i=a[0];if(a[1]<cs[i].length){const c=cs[i][a[1]++];lo[d.vertex[c]]=tick++;q.push([c,0])}
   else{hi[d.vertex[i]]=tick;q.pop()}}
  return {lo,hi};
 }
 const inside=(t,g,v)=>t.lo[g]>=0&&t.lo[g]<=t.lo[v]&&t.lo[v]<t.hi[g];
 function reach(g,start,patch=new Map()){
  const seen=new Uint8Array(g.adj.length),q=[start];seen[start]=1;let total=0;
  for(let i=0;i<q.length;i++){const u=q[i];total+=g.weights[u];for(const v of patch.has(u)?[patch.get(u)]:g.adj[u])if(!seen[v]){seen[v]=1;q.push(v)}}
  return {seen,total};
 }
 // D is the exact lost set of an empty-value cut. Restore only nodes in D
 // reachable from the replacement inside D; the old value edges stay cut.
 function score(g,t,gate,target,upper,budget={left:Infinity}){
  if(!inside(t,gate,target))return upper;
  const seen=new Uint8Array(g.adj.length),q=[target];seen[target]=1;let rescued=0;
  for(let i=0;i<q.length;i++){const u=q[i];rescued+=g.weights[u];if(u===gate)continue;
   for(const v of g.adj[u]){if(--budget.left<0)return null;if(!seen[v]&&inside(t,gate,v)){seen[v]=1;q.push(v)}}}
  need(rescued<=upper,"invalid rescue");return upper-rescued;
 }
 function cycleSafe(g,owner,target,cap){
  const seen=new Uint8Array(g.adj.length),q=[target];seen[target]=1;let edges=0;
  for(let i=0;i<q.length;i++){const u=q[i];if(u===owner)return "cycle";
   for(const v of g.adj[u]){if(++edges>cap)return "budget";if(!seen[v]){seen[v]=1;q.push(v)}}}
  return "safe";
 }
 function discover(g,opt={}){
  const scanLimit=opt.scanLimit??12000,pairLimit=opt.pairLimit??3000,limit=opt.shortlistLimit??64,budget={left:opt.scoreEdges??60000000};
  const b=cut.bounds(g),t=intervals(b.d,g.adj.length),base=reach(g,g.superRoot);
  need(b.d.count===g.adj.length&&base.total===b.total,"incomplete scope");
  const roots=new Set(g.rootIds),raw=[];let sites=0,truncated=0;
  for(let i=0;i<g.gates.length;i++){
   const {id,gate}=g.gates[i],upper=b.gains[i],sig=g.sig[id];if(!upper||sig===undefined)continue;sites++;
   const seen=new Set(),consider=(target,via)=>{
    if(target===id||roots.has(target)||g.sig[target]!==sig||seen.has(target))return;
    seen.add(target);raw.push({id,gate,target,via,upper,source:g.names[id],replacement:g.names[target]});
   };
   const direct=g.adj[gate];for(const v of direct)consider(v,null);
   let scanned=0,stop=false;
   for(const v of direct){const mid=g.gateOf.get(v);if(mid===undefined||v===id)continue;
    for(const w of g.adj[mid]){if(++scanned>scanLimit){stop=true;break}consider(w,v)}if(stop)break}
   if(stop)truncated++;
  }
  const cmp=(a,b)=>a.source<b.source?-1:a.source>b.source?1:a.replacement<b.replacement?-1:a.replacement>b.replacement?1:0;
  raw.sort((a,b)=>b.upper-a.upper||Number(a.via!==null)-Number(b.via!==null)||cmp(a,b));
  let scored=0,zero=0,budgetSkipped=0;const ranked=[];
  for(const c of raw.slice(0,pairLimit)){
   const net=score(g,t,c.gate,c.target,c.upper,budget);if(net===null){budgetSkipped++;continue}
   scored++;if(!net){zero++;continue}ranked.push({...c,net});
  }
  ranked.sort((a,b)=>b.net-a.net||Number(a.via!==null)-Number(b.via!==null)||cmp(a,b));
  const shortlist=[],perSite=new Map();let cycles=0,cycleBudget=0,checks=0;
  for(const c of ranked){
   if(shortlist.length>=limit||checks>=4*limit)break;
   if((perSite.get(c.id)||0)>=2)continue;checks++;
   const guard=cycleSafe(g,c.id,c.target,opt.cycleEdges??2000000);
   if(guard==="cycle"){cycles++;continue}if(guard==="budget"){cycleBudget++;continue}
   need(base.total-reach(g,g.superRoot,new Map([[c.gate,c.target]])).total===c.net,"independent score mismatch");
   perSite.set(c.id,(perSite.get(c.id)||0)+1);shortlist.push({...c,index:shortlist.length});
  }
  return {base,shortlist,stats:{positive_cut_public_sites:sites,signature_matches:raw.length,scored,zero_gain:zero,positive_scored:ranked.length,
   omitted_pair_budget:Math.max(0,raw.length-pairLimit),omitted_rescue_budget:budgetSkipped,truncated_sites:truncated,
   cycle_checks:checks,cycle_rejected:cycles,cycle_budget_rejected:cycleBudget,shortlisted:shortlist.length,independent_replays:shortlist.length}};
 }
 function joint(g,cs){
  const base=reach(g,g.superRoot),p=new Map(),chosen=[];let total=base.total;
  for(const c of cs){if(p.has(c.gate))continue;p.set(c.gate,c.target);const next=reach(g,g.superRoot,p).total;
   if(next<total){chosen.push({index:c.index,source:c.source,target:c.replacement,marginal:total-next,individual:c.net});total=next}else p.delete(c.gate)}
  const per_root=g.rootIds.map((r,i)=>{const a=reach(g,r),b=reach(g,r,p);
   for(let j=0;j<g.n;j++)need(!b.seen[j]||a.seen[j],"shortcut containment violated");
   return {name:g.roots[i],before:a.total,after:b.total,net:a.total-b.total}});
  return {before:base.total,after:total,net:base.total-total,independent_sum:chosen.reduce((s,c)=>s+c.individual,0),chosen,per_root};
 }
 function report(g,opt={}){
  const d=discover(g,opt);
  return {schema:1,measurement:"alias-shortcut-counterfactual-not-source-rewrite",roots:g.roots,
   baseline_project_excluding_roots:d.base.total,stats:d.stats,
   candidates:d.shortlist.map(c=>({index:c.index,source:c.source,target:c.replacement,source_module:g.module[c.id],target_module:g.module[c.target],
    witness:c.via===null?[c.source,c.replacement]:[c.source,g.names[c.via],c.replacement],
    empty_value_upper:c.upper,modeled_net:c.net,independent_replay:true,kernel_certificate:null})),
   provisional_joint:joint(g,d.shortlist)};
 }
 function render(r,lean){
  need(r.schema===1&&Array.isArray(r.candidates),"bad report");
  return "import Main\n"+lean+"\n"+r.candidates.map((c,i)=>{
   need(c.index===i&&safe(c.source)&&safe(c.target),"bad candidate");
   return "#proofopt_alias "+i+" "+JSON.stringify(c.source)+" "+JSON.stringify(c.target);
  }).join("\n")+"\n";
 }
 function parse(r,log){
  const m=new Map();for(const line of log.split(/\r?\n/)){const a=line.match(/PROOFOPT_ALIAS_(PASS|REJECT) ([0-9]+)(?:\s|$)/);if(!a)continue;
   const i=Number(a[2]);need(i<r.candidates.length&&!m.has(i),"duplicate/unexpected outcome");m.set(i,a[1]==="PASS")}
  need(m.size===r.candidates.length,"missing outcomes");
  return {schema:1,input_sha256:r.input_sha256,scope_sha256:r.scope_sha256,attempted:m.size,certified:[...m.values()].filter(Boolean).length,
   results:r.candidates.map(c=>({index:c.index,source:c.source,target:c.target,passed:m.get(c.index)}))};
 }
 function replay(g,fresh,cert,opt={}){
  need(cert.schema===1&&cert.input_sha256===fresh.input_sha256&&cert.scope_sha256===fresh.scope_sha256,"certificate provenance mismatch");
  const d=discover(g,opt),list=cert.results;need(Array.isArray(list)&&list.length===d.shortlist.length&&cert.attempted===list.length,"certificate count mismatch");
  const good=[];for(let i=0;i<list.length;i++){const x=list[i],c=d.shortlist[i];need(x.index===i&&x.source===c.source&&x.target===c.replacement&&typeof x.passed==="boolean","candidate mismatch");if(x.passed)good.push(c)}
  need(good.length===cert.certified,"certified count mismatch");
  return {schema:1,measurement:"kernel-certified-alias-counterfactual-not-source-rewrite",...fresh,attempted:list.length,certified:good.length,
   joint:joint(g,good),actual_dependency_reduction:null,actual_dag_reduction:null,actual_cpu_reduction:null};
 }
 function selfTest(){
  let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"test "+n+": "+JSON.stringify([a,b]));n++};
  const fail=f=>{let x=false;try{f()}catch{x=true}eq(x,true)};
  const row=(name,value=[],type=[],kernel=[],project=true,kind="thm")=>({record:"decl",name,module:"M."+name,project,kind,value,type,kernel});
  function build(rows,roots){const g=graph(new Map(rows.map(r=>[r.name,{project:r.project}])),roots);for(const r of rows)g.add(r);return g.finish()}
  const g=build([row("R",["A"]),row("A",["B","X"],["T"]),row("B",[],["T"]),row("X",["Y"]),row("Y"),row("T",[],[],[],false,"def")],["R"]);
  let r=report(g);eq(r.candidates.map(c=>[c.source,c.target,c.modeled_net]),[["A","B",2]]);eq(r.provisional_joint.net,2);eq(r.provisional_joint.per_root[0].net,2);
  const hop=build([row("R",["A"]),row("A",["B","X"],["T"]),row("B",["C"]),row("C",[],["T"]),row("X"),row("T",[],[],[],false,"def")],["R"]);
  r=report(hop);eq(r.candidates[0].witness,["A","B","C"]);eq(r.candidates[0].modeled_net,2);
  const shared=build([row("R",["A","B"]),row("S",["X"]),row("A",["B","X"],["T"]),row("B",[],["T"]),row("X"),row("T",[],[],[],false,"def")],["R","S"]);
  eq(report(shared).candidates.length,0);
  const cy=build([row("R",["A"]),row("A",["B","X"]),row("B",["A"]),row("X",[],["T"]),row("T",[],[],[],false,"def")],["R"]);
  r=report(cy);eq(r.stats.cycle_rejected,1);eq(r.candidates.length,0);
  const fixed=build([row("R",["A"]),row("A",["B","X"],["T"],["X"]),row("B",[],["T"]),row("X"),row("T",[],[],[],false,"def")],["R"]);
  eq(report(fixed).candidates.length,0);
  const p=report(g);p.input_sha256="a";p.scope_sha256="b";
  eq(render(p,"import Lean").includes('#proofopt_alias 0 "A" "B"'),true);
  const cert=parse(p,"info: PROOFOPT_ALIAS_PASS 0");eq(cert.certified,1);eq(replay(g,p,cert).joint.net,2);
  eq(replay(g,p,parse(p,"PROOFOPT_ALIAS_REJECT 0")).joint.net,0);
  fail(()=>parse(p,""));fail(()=>parse(p,"PROOFOPT_ALIAS_PASS 0\nPROOFOPT_ALIAS_PASS 0"));fail(()=>replay(g,p,{...cert,input_sha256:"x"}));fail(()=>replay(g,p,{...cert,results:[{index:0,source:"A",target:"X",passed:true}]}));
  let seed=1531;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed};
  // Random cyclic and acyclic graphs, every old direct edge and every
  // two-hop editable value edge, versus the independent full traversal.
  for(let j=0;j<384;j++){
   const ns=Array.from({length:6+rnd()%15},(_,i)=>"N"+i);
   const rows=ns.map((name,i)=>row(name,[...(i+1<ns.length?[ns[i+1]]:[]),...ns.filter(()=>rnd()%9===0)],ns.filter(()=>rnd()%19===0),ns.filter(()=>rnd()%23===0),i<2||rnd()%5!==0));
   const x=build(rows,ns.slice(0,2)),b=cut.bounds(x),t=intervals(b.d,x.adj.length),base=reach(x,x.superRoot);
   eq(base.total,b.total);
   for(let i=0;i<x.gates.length;i++){const {gate}=x.gates[i];const targets=new Set(x.adj[gate]);for(const v of x.adj[gate]){const mid=x.gateOf.get(v);if(mid!==undefined)for(const w of x.adj[mid])targets.add(w)}
    for(const target of targets)eq(score(x,t,gate,target,b.gains[i]),base.total-reach(x,x.superRoot,new Map([[gate,target]])).total)}
  }
  return n;
 }
 return {graph,intervals,score,reach,discover,joint,report,render,parse,replay,selfTest};
}
module.exports=engine(require('./value_cut.cjs'));

async function cli(){
 const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto"),readline=require("node:readline");
 const api=module.exports,args=process.argv.slice(2),read=p=>JSON.parse(fs.readFileSync(p,"utf8")),write=(p,x)=>fs.writeFileSync(p,JSON.stringify(x,null,2)+"\n");
 if(args[0]==="--self-test"){console.log("PASS "+api.selfTest()+" assertions");return}
 if(args[0]==="--render"&&args.length===4){fs.writeFileSync(args[3],api.render(read(args[1]),fs.readFileSync(args[2],"utf8")));return}
 if(args[0]==="--parse"&&args.length===4){const c=api.parse(read(args[1]),fs.readFileSync(args[2],"utf8"));write(args[3],c);console.log(JSON.stringify(c));return}
 const replay=args[0]==="--replay";if(replay)args.shift();
 if(args.length!==(replay?5:4))throw Error("usage: alias_pass.cjs [--replay] GRAPH.gz SHA256 SCOPE_DIR OUTPUT.json [CERT.json]");
 const [file,expected,dir,out,certFile]=args,s=read(path.join(dir,"scope.json")),raw=fs.readFileSync(path.join(dir,"scope.tsv"),"utf8");
 const sha=x=>crypto.createHash("sha256").update(x).digest("hex");
 if(s.input_sha256!==expected||s.scope_sha256!==sha(raw))throw Error("scope provenance mismatch");
 const roots=s.root_names,scope=new Map();if(!Array.isArray(roots)||!roots.length||roots.length>10)throw Error("bad roots");
 for(const line of raw.trimEnd().split("\n")){
  const p=line.split("\t"),[name,m,v]=p,mask=Number(m);
  if(p.length!==3||!name||scope.has(name)||!/^\d+$/.test(m)||mask<=0||mask>=2**roots.length||!["0","1"].includes(v))throw Error("bad scope row");
  scope.set(name,{project:v==="1",mask});
 }
 const b=api.graph(scope,roots),h=crypto.createHash("sha256"),stream=fs.createReadStream(file).pipe(zlib.createGunzip());stream.on("data",x=>h.update(x));
 let header=null,rows=0;
 for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
  const r=JSON.parse(line);
  if(!header){if(r.record!=="header"||r.schema!==1||r.measurement!=="kernel-reference-graph"||JSON.stringify(r.roots)!==JSON.stringify(roots))throw Error("bad header");header=r}
  else{rows++;b.add(r)}
 }
 if(!header||h.digest("hex")!==expected||rows!==s.declarations||scope.size!==s.union_all)throw Error("graph provenance mismatch");
 const g=b.finish();
 for(let i=0;i<roots.length;i++){const w=api.reach(g,g.rootIds[i]);for(let j=0;j<g.n;j++)if(Boolean(w.seen[j])!==Boolean(scope.get(g.names[j]).mask&(1<<i)))throw Error("scope mask mismatch")}
 const fresh={input_sha256:expected,scope_sha256:s.scope_sha256};
 const result=replay?api.replay(g,fresh,read(certFile)):{...api.report(g),...fresh,environment_declarations:rows,scoped_declarations:g.n};
 if((replay?result.joint.before:result.baseline_project_excluding_roots)!==s.union_project_excluding_roots)throw Error("baseline mismatch");
 write(out,result);console.log(JSON.stringify(result));
}
if(require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
