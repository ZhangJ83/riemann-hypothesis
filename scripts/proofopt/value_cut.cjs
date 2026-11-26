'use strict';
function engine(){
  const need=(x,m)=>{if(!x)throw Error(m)};
  const unique=a=>[...new Set(a)];
  // Private gates separate editable proof-value edges from immutable type/kernel edges.
  function graph(scope,roots){
    need(Array.isArray(roots)&&roots.length>0&&new Set(roots).size===roots.length,"bad roots");
    const names=[...scope.keys()],ids=new Map(names.map((n,i)=>[n,i])),n=names.length,superRoot=n;
    const adj=Array.from({length:n+1},()=>null),module=new Array(n),gates=[],weights=Array(n+1).fill(0);
    const rootSet=new Set(roots),rootIds=roots.map(r=>{need(scope.get(r)?.project,"missing root "+r);return ids.get(r)});
    adj[superRoot]=rootIds;
    for(let i=0;i<n;i++)weights[i]=Number(scope.get(names[i]).project&&!rootSet.has(names[i]));
    function add(row){
      const id=ids.get(row.name);if(id===undefined)return;
      need(adj[id]===null,"duplicate scoped declaration "+row.name);
      need(row.record==="decl"&&row.project===scope.get(row.name).project&&typeof row.module==="string","scope mismatch "+row.name);
      const toIds=key=>{need(Array.isArray(row[key]),"missing "+key);return unique(row[key].map(s=>{const d=ids.get(s);need(d!==undefined,"scope is not closed: "+s);return d}))};
      const fixed=unique([...toIds("type"),...toIds("kernel")]),value=toIds("value");
      module[id]=row.module;
      if(row.project&&row.kind==="thm"&&!rootSet.has(row.name)&&value.length){
        const gate=adj.length;gates.push({id,gate});adj.push(value);weights.push(0);adj[id]=[...fixed,gate];
      }else adj[id]=unique([...fixed,...value]);
    }
    function finish(){need(adj.every(Array.isArray),"missing scoped declaration");return {names,ids,adj,module,gates,weights,superRoot,rootIds,roots,n}}
    return {add,finish};
  }
  // Iterative Lengauer-Tarjan with predecessor CSR and iterative path compression.
  // DFS numbering is 1-based; index 0 is sentinel.
  function dominators(adj,start){
    const size=adj.length,df=new Int32Array(size),vertex=new Int32Array(size+1),parent=new Int32Array(size+1);
    const stack=[start],pos=[0];let count=1;df[start]=1;vertex[1]=start;
    while(stack.length){
      const u=stack[stack.length-1],i=pos[pos.length-1];
      if(i===adj[u].length){stack.pop();pos.pop();continue}
      pos[pos.length-1]++;const v=adj[u][i];if(df[v])continue;
      df[v]=++count;vertex[count]=v;parent[count]=df[u];stack.push(v);pos.push(0);
    }
    const off=new Uint32Array(count+2);let edges=0;
    for(let i=1;i<=count;i++)for(const v of adj[vertex[i]]){need(df[v]>0,"DFS invariant");off[df[v]+1]++;edges++}
    need(edges<0xffffffff,"CSR edge budget exceeded");
    for(let i=1;i<off.length;i++)off[i]+=off[i-1];
    const pred=new Int32Array(edges),cursor=off.slice();
    for(let i=1;i<=count;i++)for(const v of adj[vertex[i]])pred[cursor[df[v]]++]=i;
    const semi=new Int32Array(count+1),label=new Int32Array(count+1),ancestor=new Int32Array(count+1),idom=new Int32Array(count+1);
    const head=new Int32Array(count+1),next=new Int32Array(count+1),scratch=[];
    for(let i=1;i<=count;i++){semi[i]=i;label[i]=i}
    function evalNode(v){
      if(!ancestor[v])return label[v];
      scratch.length=0;let x=v;
      while(ancestor[ancestor[x]]){scratch.push(x);x=ancestor[x]}
      for(let j=scratch.length-1;j>=0;j--){
        const y=scratch[j],a=ancestor[y];
        if(semi[label[a]]<semi[label[y]])label[y]=label[a];
        ancestor[y]=ancestor[a];
      }
      return label[v];
    }
    for(let w=count;w>=2;w--){
      for(let p=off[w];p<off[w+1];p++){const u=evalNode(pred[p]);if(semi[u]<semi[w])semi[w]=semi[u]}
      next[w]=head[semi[w]];head[semi[w]]=w;ancestor[w]=parent[w];
      let v=head[parent[w]];head[parent[w]]=0;
      while(v){const u=evalNode(v);idom[v]=semi[u]<semi[v]?u:parent[w];v=next[v]}
    }
    for(let w=2;w<=count;w++)if(idom[w]!==semi[w])idom[w]=idom[idom[w]];
    return {df,vertex,idom,count,edges};
  }
  function walk(g,start,cut=[]){
    const blocked=new Set(cut),seen=new Uint8Array(g.adj.length),todo=[start];seen[start]=1;let total=0;
    for(let i=0;i<todo.length;i++){const u=todo[i];total+=g.weights[u];if(blocked.has(u))continue;
      for(const v of g.adj[u])if(!seen[v]){seen[v]=1;todo.push(v)}}
    return {seen,total};
  }
  function bounds(g,start=g.superRoot){
    const d=dominators(g.adj,start),sum=new Uint32Array(d.count+1);
    for(let i=1;i<=d.count;i++)sum[i]=g.weights[d.vertex[i]];
    for(let i=d.count;i>=2;i--){need(d.idom[i]>0&&d.idom[i]<i,"invalid immediate dominator");sum[d.idom[i]]+=sum[i]}
    return {d,total:sum[1],gains:g.gates.map(x=>sum[d.df[x.gate]]||0)};
  }
  function analyze(g,limit=40,verify=5){
    need(Number.isInteger(limit)&&limit>0&&Number.isInteger(verify)&&verify>=0&&verify<=limit,"bad limits");
    const b=bounds(g),base=walk(g,g.superRoot);
    need(b.d.count===g.adj.length&&base.total===b.total,"scope/reachability invariant");
    const per=g.rootIds.map(id=>bounds(g,id));
    const ranked=g.gates.map(({id,gate},i)=>({name:g.names[id],module:g.module[id],gate,union_upper:b.gains[i],
      per_root_upper:per.map(p=>p.gains[i]),value_references:g.adj[gate].length})).sort((a,b)=>b.union_upper-a.union_upper||a.name.localeCompare(b.name));
    const top=ranked.filter(x=>x.union_upper>0).slice(0,limit),checked=top.slice(0,verify);
    for(const c of checked){
      const trial=walk(g,g.superRoot,[c.gate]);need(base.total-trial.total===c.union_upper,"independent union mismatch");
      for(let i=0;i<g.rootIds.length;i++)need(walk(g,g.rootIds[i],[c.gate]).total===per[i].total-c.per_root_upper[i],"independent per-root mismatch");
      const byModule=new Map(),sample=[];
      for(let i=0;i<g.n;i++)if(base.seen[i]&&!trial.seen[i]&&g.weights[i]){
        byModule.set(g.module[i],(byModule.get(g.module[i])||0)+1);if(sample.length<20)sample.push(g.names[i]);
      }
      c.independent_traversal_verified=true;c.lost_sample=sample;
      c.lost_modules=[...byModule].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0])).slice(0,10);
    }
    const batch=walk(g,g.superRoot,checked.map(c=>c.gate)),strip=({gate,...c})=>c;
    const histogram={zero:0,one:0,two_to_nine:0,ten_to_99:0,at_least_100:0};
    for(const x of ranked){const v=x.union_upper;histogram[v===0?"zero":v===1?"one":v<10?"two_to_nine":v<100?"ten_to_99":"at_least_100"]++}
    return {schema:1,measurement:"proof-value-cut-upper-bound-not-a-rewrite",root_names:g.roots,
      scoped_declarations:g.n,expanded_vertices:g.adj.length,expanded_edges:b.d.edges,editable_theorems:g.gates.length,
      baseline_union_project_excluding_all_roots:b.total,baseline_per_root_excluding_all_roots:per.map(p=>p.total),
      histogram,top:top.map(strip),verified_candidates:checked.length,
      joint_cut:{names:checked.map(c=>c.name),exact_loss:base.total-batch.total,naive_sum:checked.reduce((s,c)=>s+c.union_upper,0)},
      limitations:["Only the complete exported reference graph is modeled; no proof is synthesized.",
      "Single-site upper bound holds when all other declarations and ownership are unchanged; replacement may introduce references, restoring some lost nodes.",
      "Theorem itself is retained; its type and kernel references remain. Joint cut may overlap or have synergy, and is not a sum of single-site scores.",
      "All final roots are excluded from every count and are never editable here. Per-root metric excludes all five roots.",
      "No measured proof DAG or build CPU reduction; not an originality or upstream contribution claim."]};
  }
  function selfTest(){
    let assertions=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"test "+assertions+": "+JSON.stringify([a,b]));assertions++};
    const fail=f=>{let yes=false;try{f()}catch{yes=true}eq(yes,true)};
    const row=(name,value=[],type=[],kernel=[],project=true,kind="thm")=>({record:"decl",name,module:"M."+name,project,kind,value,type,kernel});
    function build(rows,roots){const scope=new Map(rows.map(r=>[r.name,{project:r.project}])),g=graph(scope,roots);for(const r of rows)g.add(r);return g.finish()}
    const example=build([row("R",["A","B"]),row("S",["B"]),row("A",["X","Y"],["Y"]),row("B",["X"]),row("X"),row("Y")],["R","S"]);
    let q=analyze(example);eq(q.histogram.zero,2);eq(q.top.length,0);
    eq(walk(example,example.superRoot,example.gates.map(x=>x.gate)).total,3);
    const a=build([row("R",["A"]),row("A",["X","Y"],["Y"]),row("X",["Z"]),row("Y"),row("Z")],["R"]);
    q=analyze(a);eq(q.top[0].name,"A");eq(q.top[0].union_upper,2);eq(q.top[1].name,"X");eq(q.top[1].union_upper,1);eq(q.joint_cut.exact_loss,2);eq(q.joint_cut.naive_sum,3);
    const cyc=build([row("R",["A"]),row("A",["X"]),row("X",["A"])],["R"]);eq(bounds(cyc).gains,[1,0]);
    fail(()=>build([row("R",["missing"])],["R"]));fail(()=>build([row("R"),row("R")],["R"]));
    let seed=1729;const rand=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed};
    for(let t=0;t<512;t++){
      const n=6+rand()%15,ns=Array.from({length:n},(_,i)=>"N"+i);
      const rows=ns.map((name,i)=>row(name,[...(i+1<n?[ns[i+1]]:[]),...ns.filter(()=>rand()%7===0)],ns.filter(()=>rand()%11===0),ns.filter(()=>rand()%17===0),i<2||rand()%5!==0));
      const g=build(rows,ns.slice(0,2));
      for(const start of [g.superRoot,...g.rootIds]){
        const b=bounds(g,start),base=walk(g,start);eq(b.total,base.total);
        for(let i=0;i<g.gates.length;i++)eq(b.gains[i],base.total-walk(g,start,[g.gates[i].gate]).total);
      }
    }
    const n=50000,adj=Array.from({length:n},(_,i)=>i+1<n?[i+1]:[]);
    const d=dominators(adj,0);eq(d.count,n);eq(d.idom[n],n-1);eq(d.edges,n-1);
    return assertions;
  }
  return {graph,dominators,walk,bounds,analyze,selfTest};
}
async function cli(){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto"),readline=require("node:readline");
  const api=engine(),args=process.argv.slice(2);
  if(args[0]==="--self-test"){console.log("PASS "+api.selfTest()+" assertions");return}
  if(args.length!==4)throw Error("usage: value_cut.cjs GRAPH.gz SHA256 SCOPE_DIR REPORT.json");
  const [graphPath,expected,dir,out]=args,s=JSON.parse(fs.readFileSync(path.join(dir,"scope.json"),"utf8"));
  const raw=fs.readFileSync(path.join(dir,"scope.tsv"),"utf8"),sha=x=>crypto.createHash("sha256").update(x).digest("hex");
  if(s.input_sha256!==expected||s.scope_sha256!==sha(raw))throw Error("scope provenance mismatch");
  const scope=new Map(),roots=s.root_names;
  if(!Array.isArray(roots)||roots.length<1||roots.length>10)throw Error("bad roots");
  for(const line of raw.trimEnd().split("\n")){
    const p=line.split("\t"),[name,m,v]=p,mask=Number(m);
    if(p.length!==3||!name||scope.has(name)||!/^\d+$/.test(m)||mask<=0||mask>=2**roots.length||!["0","1"].includes(v))throw Error("invalid scope row "+line);
    scope.set(name,{project:v==="1",mask});
  }
  const g=api.graph(scope,roots),h=crypto.createHash("sha256"),stream=fs.createReadStream(graphPath).pipe(zlib.createGunzip());stream.on("data",b=>h.update(b));
  let header=null,rows=0;
  for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
    const r=JSON.parse(line);
    if(!header){if(r.record!=="header"||r.schema!==1||r.measurement!=="kernel-reference-graph"||JSON.stringify(r.roots)!==JSON.stringify(roots))throw Error("bad graph header");header=r}
    else{rows++;g.add(r)}
  }
  if(!header||h.digest("hex")!==expected||rows!==s.declarations||scope.size!==s.union_all)throw Error("graph provenance mismatch");
  const expanded=g.finish();
  for(let i=0;i<roots.length;i++){
    const w=api.walk(expanded,expanded.rootIds[i]);
    for(let j=0;j<expanded.n;j++)if(Boolean(w.seen[j])!==Boolean(scope.get(expanded.names[j]).mask&(1<<i)))throw Error("scope mask mismatch "+expanded.names[j]);
  }
  const report=api.analyze(expanded);
  if(report.baseline_union_project_excluding_all_roots!==s.union_project_excluding_roots)throw Error("baseline count mismatch");
  report.input_sha256=expected;report.scope_sha256=s.scope_sha256;report.environment_declarations=rows;
  fs.writeFileSync(out,JSON.stringify(report,null,2)+"\n");
  console.log(JSON.stringify(report));
}
module.exports=engine();
if(require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
