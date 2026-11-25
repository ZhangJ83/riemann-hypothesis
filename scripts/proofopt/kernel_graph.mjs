// ProofOpt graph model. Tested in a V8 isolate; CLI uses Node.js.
// Only graph-model optimality is certified; Lean proof validity is not.
function invariant(ok, msg) { if (!ok) throw new Error(msg); }

function uniqueStrings(xs,label) {
  invariant(Array.isArray(xs)&&xs.every(x=>typeof x==="string"&&x.length>0),`invalid ${label}`);
  invariant(new Set(xs).size===xs.length,`duplicate ${label}`);
  return new Set(xs);
}

function buildGraph(snapshot) {
  invariant(snapshot.schema===1 && ["kernel-reference-graph","synthetic","source-projection"].includes(snapshot.measurement),"unsupported snapshot");
  const roots=uniqueStrings(snapshot.roots,"roots"), nodes=new Map();
  invariant(roots.size>0&&Array.isArray(snapshot.nodes),"empty roots or invalid nodes");
  for(const n of snapshot.nodes) {
    invariant(typeof n.name==="string"&&n.name.length>0&&!nodes.has(n.name),"invalid or duplicate node");
    invariant(typeof n.project==="boolean"&&typeof n.kind==="string"&&typeof n.module==="string","invalid node metadata");
    nodes.set(n.name,{...n,type:new Set(uniqueStrings(n.type,"type references")),value:new Set(uniqueStrings(n.value,"value references")),kernel:new Set(uniqueStrings(n.kernel,"kernel references"))});
  }
  for(const r of roots) invariant(nodes.has(r),`missing root ${r}`);
  for(const n of nodes.values()) for(const d of [...n.type,...n.value,...n.kernel]) invariant(nodes.has(d),`unresolved reference ${n.name} -> ${d}`);
  return {roots,nodes,measurement:snapshot.measurement};
}

function reach(g, roots=g.roots, edits=new Map()) {
  const seen=new Set(), stack=[...roots];
  while(stack.length) {
    const name=stack.pop();
    if(seen.has(name)) continue;
    seen.add(name); const n=g.nodes.get(name);
    for(const d of n.type) if(!seen.has(d)) stack.push(d);
    for(const d of n.kernel) if(!seen.has(d)) stack.push(d);
    for(const d of edits.get(name)??n.value) if(!seen.has(d)) stack.push(d);
  }
  return seen;
}

function summarize(g, live) {
  return {total:live.size,project:[...live].filter(n=>g.nodes.get(n).project).length,
    axioms:[...live].filter(n=>g.nodes.get(n).kind==="axiom").sort(),
    project_names:[...live].filter(n=>g.nodes.get(n).project).sort()};
}

function validateCandidates(g, candidates) {
  invariant(Array.isArray(candidates),"candidates must be array"); const ids=new Set();
  return candidates.map(c=>{
    invariant(typeof c.id==="string"&&c.id&&!ids.has(c.id),"duplicate/invalid candidate id"); ids.add(c.id);
    const n=g.nodes.get(c.decl);
    invariant(n&&n.project&&n.kind==="thm"&&!g.roots.has(c.decl),`not an editable non-root project theorem: ${c.decl}`);
    invariant(Number.isSafeInteger(c.cost)&&c.cost>0,"invalid candidate cost");
    const old=uniqueStrings(c.before,"before"), next=uniqueStrings(c.after,"after");
    invariant(old.size===n.value.size&&[...old].every(x=>n.value.has(x)),`stale before set: ${c.id}`);
    invariant([...next].every(x=>g.nodes.has(x)),`unknown dependency: ${c.id}`);
    invariant(next.size!==old.size||[...next].some(x=>!old.has(x)),`no-op candidate: ${c.id}`);
    invariant(!next.has(c.decl),"direct self reference");
    return {...c,after:next};
  });
}

function introducesCycle(g, edits) {
  // Baseline inductive metadata can contain legitimate cycles. A replacement
  // must not introduce a cycle through a newly added proof-value dependency.
  for(const [name,after] of edits) for(const d of after) {
    if(!g.nodes.get(name).value.has(d)&&reach(g,[d],edits).has(name)) return true;
  }
  return false;
}

function evaluate(g, candidates) {
  const edits=new Map();
  for(const c of candidates) {invariant(!edits.has(c.decl),"conflicting declaration alternatives"); edits.set(c.decl,c.after);}
  if(introducesCycle(g,edits)) return {valid:false,reason:"new dependency cycle"};
  const old=reach(g), now=reach(g,g.roots,edits), b=summarize(g,old), a=summarize(g,now);
  const newAxioms=a.axioms.filter(x=>!b.axioms.includes(x));
  if(newAxioms.length) return {valid:false,reason:"new reachable axioms",newAxioms};
  return {valid:true,removed:b.project_names.filter(x=>!now.has(x)),added:a.project_names.filter(x=>!old.has(x)),
    net:b.project-a.project,before:b.project,after:a.project,
    per_root:[...g.roots].map(r=>{const x=summarize(g,reach(g,[r])),y=summarize(g,reach(g,[r],edits));return {root:r,before:x.project,after:y.project,net:x.project-y.project};})};
}

function optimize(g, raw, budget, maxStates=100000) {
  invariant(Number.isSafeInteger(budget)&&budget>=0&&Number.isSafeInteger(maxStates)&&maxStates>0,"invalid budget/state limit");
  const candidates=validateCandidates(g,raw).sort((a,b)=>a.id<b.id?-1:a.id>b.id?1:0);
  // Group mutually exclusive alternatives; enumerate feasible combinations only.
  const groups=new Map();
  for(const c of candidates) {if(!groups.has(c.decl)) groups.set(c.decl,[]);groups.get(c.decl).push(c);}
  const blocks=[...groups.values()], todo=[{i:0,cost:0,selected:[]}];
  let visited=0,evaluated=0,invalid=0,best=null;
  while(todo.length) {
    const s=todo.pop(); if(++visited>maxStates) throw new Error("state limit exceeded; no optimum certified");
    if(s.i===blocks.length) {
      evaluated++;const result=evaluate(g,s.selected);
      if(!result.valid){invalid++;continue;}
      const ids=s.selected.map(c=>c.id).sort();
      if(!best||result.net>best.result.net||(result.net===best.result.net&&(s.cost<best.cost||(s.cost===best.cost&&JSON.stringify(ids)<JSON.stringify(best.ids))))) best={ids,cost:s.cost,result};
      continue;
    }
    todo.push({i:s.i+1,cost:s.cost,selected:s.selected});
    for(const c of blocks[s.i]) if(s.cost+c.cost<=budget) todo.push({i:s.i+1,cost:s.cost+c.cost,selected:[...s.selected,c]});
  }
  return {measurement:g.measurement,certified_model_optimum:true,visited,evaluated,invalid,best,warning:"Graph simulation only. Replacement proofs, type equivalence, kernel acceptance, expression DAG and CPU savings require independent checks."};
}

function readSnapshot(text) {
  const rows=text.trim().split(/\r?\n/).map(l=>JSON.parse(l));
  invariant(rows.length>1&&rows[0].record==="header","missing snapshot header");
  const {record,...meta}=rows[0];
  return {...meta,nodes:rows.slice(1).map(r=>{invariant(r.record==="decl","invalid record");const {record,...n}=r;return n;})};
}

function testSuite(real) {
  let passed=0,randomCases=0; const results=[];
  const eq=(a,b)=>invariant(JSON.stringify(a)===JSON.stringify(b),`expected ${JSON.stringify(b)}, got ${JSON.stringify(a)}`);
  const test=(name,f)=>{f();passed++;results.push(name);};
  const n=(name,value=[],type=[],kernel=[],kind="thm",project=true)=>({name,value,type,kernel,kind,project,module:project?"Main":"External"});
  const graph=(nodes,roots=["R"])=>buildGraph({schema:1,measurement:"synthetic",roots,nodes});
  const candidate=(id,decl,before,after,cost=1)=>({id,decl,before,after,cost});
  const throws=(f,needle)=>{let caught=false;try{f();}catch(e){caught=String(e).includes(needle);}invariant(caught,`expected error: ${needle}`);};
  test("shared dependency requires both edits",()=>{const g=graph([n("R",["A","B"]),n("A",["X"]),n("B",["X"]),n("X",["Y"]),n("Y")]);const cs=[candidate("a","A",["X"],[]),candidate("b","B",["X"],[])];eq(optimize(g,cs,1).best.result.net,0);eq(optimize(g,cs,2).best.result.net,2);});
  test("type and kernel references cannot be removed",()=>{const g=graph([n("R",["A"]),n("A",["X"],["X"],["Y"]),n("X"),n("Y")]);eq(optimize(g,[candidate("a","A",["X"],[])],1).best.result.net,0);});
  test("external traversal is not a free dependency hiding trick",()=>{const g=graph([n("R",["A"]),n("A",["X"]),n("X"),n("E",["Y"],[],[],"def",false),n("Y")]);const x=evaluate(g,validateCandidates(g,[candidate("a","A",["X"],["E"])]));eq(x.net,0);eq(x.added,["Y"]);});
  test("pre-existing dead declarations are excluded",()=>{const g=graph([n("R",["A"]),n("A",["X"]),n("X"),n("Dead")]);eq(optimize(g,[candidate("a","A",["X"],[])],1).best.result.removed,["X"]);});
  test("multi-root closure and individual net",()=>{const g=graph([n("R",["A"]),n("S",["X"]),n("A",["X"]),n("X")],["R","S"]);const x=evaluate(g,validateCandidates(g,[candidate("a","A",["X"],[])]));eq(x.net,0);eq(x.per_root.map(r=>r.net),[1,0]);});
  test("new axiom rejected",()=>{const g=graph([n("R",["A"]),n("A",["X"]),n("X"),n("Bad",[],[],[],"axiom",false)]);eq(evaluate(g,validateCandidates(g,[candidate("a","A",["X"],["Bad"])] )).valid,false);});
  test("new cycle rejected; baseline metadata cycles allowed",()=>{const g=graph([n("R",["A","I"]),n("A",["X"]),n("X",["A"]),n("I",[],[],["C"],"ind"),n("C",[],[],["I"],"ctor"),n("B",["A"])]);eq(evaluate(g,validateCandidates(g,[candidate("a","A",["X"],["B"])] )).valid,false);eq(reach(g).has("C"),true);});
  test("alternatives conflict and budget is weighted",()=>{const g=graph([n("R",["A"]),n("A",["X","Y"]),n("X"),n("Y")]);const cs=[candidate("cheap","A",["X","Y"],["Y"]),candidate("full","A",["X","Y"],[],2)];eq(optimize(g,cs,1).best.ids,["cheap"]);eq(optimize(g,cs,2).best.ids,["full"]);eq(optimize(g,cs,3).evaluated,3);});
  test("stale replacement, protected roots and missing refs fail closed",()=>{const g=graph([n("R",["A"]),n("A",["X"]),n("X")]);throws(()=>validateCandidates(g,[candidate("x","A",[],["X"])]),"stale");throws(()=>validateCandidates(g,[candidate("x","R",["A"],[])]),"not an editable");throws(()=>graph([n("R",["missing"])]),"unresolved");});
  test("truncated enumeration cannot certify optimality",()=>{const g=graph([n("R",["A"]),n("A",["X"]),n("X")]);throws(()=>optimize(g,[candidate("a","A",["X"],[])],1,1),"no optimum certified");});
  test("JSONL parser roundtrip",()=>{const r=readSnapshot(JSON.stringify({record:"header",schema:1,measurement:"synthetic",roots:["R"]})+"\n"+JSON.stringify({record:"decl",...n("R")}));eq(reach(buildGraph(r)).size,1);});
  test("independent exhaustive random oracle",()=>{
    let seed=9357;const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    for(let k=0;k<240;k++){
      const names=["R","A","B","C","D","E","F","G","H"], rows=names.map((x,i)=>n(x,names.slice(i+1).filter(()=>rnd()<.32)));
      rows[0].value=["A","B","C"];const g=graph(rows), cs=rows.slice(1).filter(x=>x.value.length).map(x=>candidate(x.name,x.name,x.value,[],1+Math.floor(rnd()*3)));
      const budget=Math.floor(rnd()*7), baseline=reach(g).size;let oracle=0;
      for(let mask=0;mask<2**cs.length;mask++){
        const chosen=cs.filter((_,i)=>mask&(1<<i));if(chosen.reduce((s,c)=>s+c.cost,0)>budget)continue;
        const dropped=new Set(chosen.map(c=>c.decl)),seen=new Set(["R"]);let changed=true;
        while(changed){changed=false;for(const row of rows)if(seen.has(row.name)&&!dropped.has(row.name))for(const d of row.value)if(!seen.has(d)){seen.add(d);changed=true;}}
        oracle=Math.max(oracle,baseline-seen.size);
      }
      eq(optimize(g,cs,budget).best.result.net,oracle);randomCases++;
    }
  });
  test("pinned Main source projection integration",()=>{const g=buildGraph(real);eq(g.roots.size,5);eq(reach(g).size,5);eq([...g.nodes.values()].reduce((s,x)=>s+x.value.size,0),4);eq(reach(g,["riemannZeta_eq_zero_re"]).size,3);eq(reach(g,["LFunction_eq_zero_re_of_isPrimitive"]).size,3);});
  return {passed,randomCases,tests:results};
}

export {buildGraph,reach,summarize,validateCandidates,evaluate,optimize,readSnapshot,testSuite};
