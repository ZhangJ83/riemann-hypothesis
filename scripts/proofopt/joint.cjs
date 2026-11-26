'use strict';
function jointEngine(){
 const need=(b,m)=>{if(!b)throw Error(m)};
 // Candidate gates are terminals. Each root and gate option becomes a source.
 // A node's signature is the set of sources that can reach it without crossing
 // another candidate gate. Weighted signature aggregation is lossless.
 function quotient(g,groups){
  const gateIndex=new Map(groups.map((x,i)=>[x.gate,i]));
  const sources=g.rootIds.map(id=>[id]),choices=[];
  for(const group of groups){
   const ix=[];for(const refs of [g.adj[group.gate],...group.options.map(o=>o.ids)]){ix.push(sources.length);sources.push(refs)}
   choices.push(ix);
  }
  need(sources.length<=30,"source mask budget exceeded");
  need(groups.every(x=>g.weights[x.gate]===0),"weighted gate");
  const masks=new Uint32Array(g.adj.length),next=new Uint32Array(sources.length),seen=new Int32Array(g.adj.length);
  let edges=0;
  for(let i=0;i<sources.length;i++){
   const bit=1<<i,q=[];for(const u of sources[i])if(seen[u]!==i+1){seen[u]=i+1;q.push(u)}
   for(let j=0;j<q.length;j++){
    const u=q[j],gate=gateIndex.get(u);masks[u]|=bit;
    if(gate!==undefined){next[i]|=1<<gate;continue}
    for(const v of g.adj[u]){edges++;if(seen[v]!==i+1){seen[v]=i+1;q.push(v)}}
   }
  }
  const hist=new Map();for(let i=0;i<masks.length;i++)if(g.weights[i])hist.set(masks[i],(hist.get(masks[i])??0)+g.weights[i]);
  const bins=[...hist].filter(([m])=>m!==0);
  const all=(1<<g.rootIds.length)-1;
  function evaluate(selection,roots=all){
   let active=roots,done=0;
   while(true){
    let terminals=0;for(let i=0;i<sources.length;i++)if(active&(1<<i))terminals|=next[i];
    const fresh=terminals&~done;if(!fresh)break;
    for(let i=0;i<groups.length;i++)if(fresh&(1<<i))active|=1<<choices[i][selection[i]];
    done|=fresh;
   }
   let weight=0;for(const [mask,w] of bins)if(mask&active)weight+=w;
   return weight;
  }
  return {evaluate,sources:sources.length,bins:bins.length,edges};
 }
 function optimize(g,groups,api,limit=65536){
  need(Number.isSafeInteger(limit)&&limit>=1,"bad state budget");
  const q=quotient(g,groups),zero=groups.map(()=>0),base=q.evaluate(zero),patch=s=>new Map(groups.flatMap((c,i)=>s[i]?[ [c.gate,c.options[s[i]-1].ids] ]:[]));
  const direct=(s,id)=>api.reach(g,id,patch(s));
  need(direct(zero,g.superRoot).weight===base,"quotient baseline mismatch");
  const space=groups.reduce((n,c)=>n*BigInt(c.options.length+1),1n);
  const individual=[];
  for(let i=0;i<groups.length;i++)for(let j=1;j<=groups[i].options.length;j++){
   const s=zero.slice();s[i]=j;const w=q.evaluate(s);
   need(direct(s,g.superRoot).weight===w,"single-option quotient mismatch");
   individual.push({i,j,gain:base-w,index:groups[i].options[j-1].index});
  }
  // Same positive-singleton greedy baseline as Round 20.
  const greedy=zero.slice();let gw=base;
  for(const x of individual.slice().sort((a,b)=>b.gain-a.gain||a.index-b.index)){
   if(x.gain<=0||greedy[x.i])continue;
   greedy[x.i]=x.j;const w=q.evaluate(greedy);
   if(w<gw)gw=w;else greedy[x.i]=0;
  }
  let best=greedy.slice(),bw=gw,states=0;
  const count=s=>s.reduce((n,x)=>n+Number(x!==0),0);
  function test(s){const w=q.evaluate(s);states++;
   if(w<bw||(w===bw&&count(s)<count(best))){best=s.slice();bw=w}}
  if(space<=BigInt(limit)){
   const s=zero.slice();
   while(true){test(s);let i=0;for(;i<s.length;i++){s[i]++;if(s[i]<=groups[i].options.length)break;s[i]=0}if(i===s.length)break}
  }else{
   // Budgeted fallback, not an optimality certificate. Evaluate zero,
   // full first-option batch, and pairwise moves around the greedy seed.
   test(zero);if(states<limit)test(groups.map(c=>Number(c.options.length>0)));
   outer:for(let i=0;i<groups.length;i++)for(let j=i;j<groups.length;j++)
    for(let a=0;a<=groups[i].options.length;a++)for(let b=0;b<=groups[j].options.length;b++){
     if(states>=limit)break outer;if(i===j&&a!==b)continue;
     const s=greedy.slice();s[i]=a;s[j]=b;test(s)
    }
  }
  need(direct(best,g.superRoot).weight===bw,"selected quotient mismatch");
  const per_root=g.rootIds.map((id,i)=>{
   const a=direct(zero,id),b=direct(best,id);
   need(q.evaluate(best,1<<i)===b.weight,"per-root quotient mismatch");
   for(let j=0;j<g.n;j++)need(!b.seen[j]||a.seen[j],"closure expanded");
   return {name:g.roots[i],before:a.weight,after:b.weight,net:a.weight-b.weight};
  });
  const chosen=best.flatMap((j,i)=>j?[groups[i].options[j-1]]:[]);
  return {before:base,after:bw,net:base-bw,greedy_net:base-gw,additional_net:gw-bw,
   exact:space<=BigInt(limit),configuration_space:space.toString(),states,source_count:q.sources,signature_bins:q.bins,
   quotient_edges_scanned:q.edges,individual,chosen,per_root};
 }
 function replay(g,report,cert,opt={}){
  const api=opt.api??require("./parametric.cjs");
  need(cert.schema===1&&cert.input_sha256===report.input_sha256&&cert.scope_sha256===report.scope_sha256,"provenance mismatch");
  need(cert.results.length===report.candidates.length,"candidate count mismatch");
  const gates=new Map(g.gates.map(x=>[x.id,x.gate])),map=new Map(),rejected={};
  const reject=k=>{rejected[k]=(rejected[k]??0)+1};
  for(let i=0;i<cert.results.length;i++){
   const c=cert.results[i],e=report.candidates[i];need(c.index===i&&c.source===e.source&&c.target===e.target,"candidate mismatch");
   if(c.refs===null){reject(c.outcome==="inconclusive"?"inconclusive":"kernel-reject");continue}
   need(Array.isArray(c.refs)&&c.refs.every(x=>typeof x==="string")&&c.refs.includes(c.target),"bad certificate");
   const owner=g.ids.get(c.source),gate=gates.get(owner),ids=[...new Set(c.refs.map(n=>g.ids.get(n)))];
   if(gate===undefined||ids.some(x=>x===undefined)){reject("missing-graph-reference");continue}
   const status=api.guard(g,owner,ids,opt.edgeBudget);if(status!=="safe"){reject(status);continue}
   if(!map.has(gate))map.set(gate,{gate,options:[]});map.get(gate).options.push({...c,ids});
  }
  const groups=[...map.values()];
  // Fail closed rather than silently discard certified candidates.
  const result=optimize(g,groups,api,opt.stateBudget);
  return {...result,schema:1,measurement:"kernel-certified-joint-counterfactual-not-source-rewrite",
   input_sha256:report.input_sha256,scope_sha256:report.scope_sha256,attempted:cert.results.length,
   kernel_pass:cert.results.filter(c=>c.refs!==null).length,rejected,actual_dependency_reduction:null,actual_dag_reduction:null,actual_cpu_reduction:null};
 }
 function selfTest(api){
  let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"assertion "+n+" "+JSON.stringify([a,b]));n++};
  const graph=(adj,weights,roots)=>({adj,weights,rootIds:roots,roots:roots.map(String),superRoot:adj.length-1,n:adj.length-1});
  // Two zero-gain cuts together remove X. Both roots must remain covered.
  let g=graph([[2],[3],[5],[6],[],[4],[4],[0,1]],[0,0,1,1,1,0,0,0],[0,1]);
  let groups=[{gate:5,options:[{index:0,ids:[]}]},{gate:6,options:[{index:1,ids:[]}]}];
  let x=optimize(g,groups,api);eq(x.greedy_net,0);eq(x.net,1);eq(x.exact,true);eq(x.states,4);eq(x.chosen.length,2);eq(x.per_root.map(x=>x.net),[1,1]);
  x=optimize(g,groups,api,2);eq(x.exact,false);eq(x.net,1);eq(x.states,2);
  let seed=58171;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed};
  let configs=0;
  for(let t=0;t<320;t++){
   const k=6+rnd()%7,adj=Array.from({length:k},(_,i)=>Array.from({length:k},(_,j)=>j).filter(j=>i!==j&&rnd()%7===0));
   const weights=adj.map(()=>rnd()%2);weights[0]=weights[1]=0;
   const gateIds=[2,3,4];for(const v of gateIds)weights[v]=0;
   groups=gateIds.map((gate,i)=>({gate,options:[{index:2*i,ids:adj[gate].filter(()=>rnd()%2===0)},{index:2*i+1,ids:adj[gate].filter(()=>rnd()%3===0)}]}));
   adj.push([0,1]);weights.push(0);g=graph(adj,weights,[0,1]);
   const q=quotient(g,groups);let min=Infinity;
   for(let a=0;a<3;a++)for(let b=0;b<3;b++)for(let c=0;c<3;c++){
    const s=[a,b,c],patch=new Map(groups.flatMap((v,i)=>s[i]?[[v.gate,v.options[s[i]-1].ids]]:[]));
    for(const [id,mask] of [[0,1],[1,2],[g.superRoot,3]]){const d=api.reach(g,id,patch).weight;eq(q.evaluate(s,mask),d);if(mask===3)min=Math.min(min,d)}
    configs++;
   }
   x=optimize(g,groups,api);eq(x.after,min);eq(x.exact,true);eq(x.net>=x.greedy_net,true);
  }
  return {assertions:n,random_graphs:320,configurations:configs};
 }
 return {quotient,optimize,replay,selfTest};
}
module.exports=jointEngine();
if(require.main===module)console.log(JSON.stringify(module.exports.selfTest(require('./parametric.cjs'))));
