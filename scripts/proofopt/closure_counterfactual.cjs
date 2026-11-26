'use strict';
function proofopt(){
  "use strict";
  const ROOTS=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
  function assert(x,msg){if(!x)throw Error(msg)}
  function graph(){
    const ids=new Map(),names=[],rows=[];
    function intern(s){assert(typeof s==="string"&&s.length,"invalid reference name");if(!ids.has(s)){ids.set(s,names.length);names.push(s)}return ids.get(s)}
    function add(r){
      assert(r.record==="decl"&&typeof r.project==="boolean"&&typeof r.module==="string","invalid declaration");
      const id=intern(r.name);assert(!rows[id],"duplicate "+r.name);
      for(const k of ["type","kernel","value"])assert(Array.isArray(r[k]),"missing edge category "+k+" in "+r.name);
      const fixed=[...new Set([...r.type,...r.kernel].map(intern))],value=[...new Set(r.value.map(intern))];
      rows[id]={project:r.project,module:r.module,kind:r.kind,deps:[...new Set([...fixed,...value])],
        ...(r.project?{fixed,value}:{})};
      return id;
    }
    return {ids,names,rows,add};
  }
  function walk(g,roots,patch=new Map()){
    const seen=new Set(),todo=[...roots],missing=[],project=new Set();
    while(todo.length){const id=todo.pop();if(seen.has(id))continue;seen.add(id);
      const row=g.rows[id];if(!row){missing.push(id);continue}
      if(row.project)project.add(id);
      for(const d of patch.get(id)??row.deps)if(!seen.has(d))todo.push(d);
    }
    return {seen,missing,project};
  }
  function delta(g,a,b,roots){
    const rs=new Set(roots),removed=[...a.project].filter(x=>!rs.has(x)&&!b.project.has(x)),added=[...b.project].filter(x=>!rs.has(x)&&!a.project.has(x));
    const before=[...a.project].filter(x=>!rs.has(x)).length,after=[...b.project].filter(x=>!rs.has(x)).length;
    return {before,after,net_removed:before-after,removed_count:removed.length,added_count:added.length,
      removed_sample:removed.map(x=>g.names[x]).sort().slice(0,30),added_sample:added.map(x=>g.names[x]).sort().slice(0,30),
      missing_before:a.missing.length,missing_after:b.missing.length,
      status:a.missing.length||b.missing.length?"incomplete_reference_graph":"reference_graph_model_only"};
  }
  function plan(g,roots,pairs,base=null){
    base??=walk(g,roots);
    const mapping=new Map(),replacements=new Set();
    for(const p of pairs){
      const a=g.ids.get(p.from),b=g.ids.get(p.to);
      if(a===undefined||b===undefined||!g.rows[a]||!g.rows[b])return {status:"unknown_endpoint",pairs};
      if(a===b||roots.includes(a)||!g.rows[a].project||!g.rows[b].project||g.rows[a].kind!=="thm"||g.rows[b].kind!=="thm"||mapping.has(a))
        return {status:"invalid_endpoint",pairs};
      mapping.set(a,b);replacements.add(b);
    }
    for(const x of replacements)if(mapping.has(x))return {status:"chained_or_cyclic_aliases_unsupported",pairs};
    const patch=new Map(),callers=[],introduced=new Map();
    for(let i=0;i<g.rows.length;i++){
      const r=g.rows[i];if(!r?.project)continue;
      const changed=r.value.filter(x=>mapping.has(x));if(!changed.length)continue;
      const next=new Set([...r.fixed,...r.value.map(x=>mapping.get(x)??x)]);
      const old=new Set(r.deps);
      if(next.size===old.size&&[...next].every(x=>old.has(x)))continue;
      patch.set(i,[...next]);callers.push(i);
      for(const d of next)if(!old.has(d)){
        if(!introduced.has(d))introduced.set(d,new Set());introduced.get(d).add(i);
      }
    }
    // Only newly inserted dependency edges can create cycles in a previously valid graph.
    // Check the new graph, not the old graph, and reject even unreachable new cycles.
    for(const [d,cs] of introduced){
      const reachable=walk(g,[d],patch).seen;
      for(const c of cs)if(reachable.has(c))return {status:"new_dependency_cycle",pairs,cycle_edge:[g.names[c],g.names[d]]};
    }
    const next=walk(g,roots,patch);
    const perRoot=Object.fromEntries(roots.map(r=>[g.names[r],delta(g,walk(g,[r]),walk(g,[r],patch),[r])]));
    return {status:"modeled_not_typechecked",pairs,union:delta(g,base,next,roots),per_root:perRoot,
      changed_project_callers:callers.length,changed_live_callers:callers.filter(x=>base.seen.has(x)).length,
      caller_sample:callers.map(x=>({name:g.names[x],module:g.rows[x].module})).sort((a,b)=>a.name.localeCompare(b.name)).slice(0,30),
      victims_still_live:[...mapping.keys()].filter(x=>next.seen.has(x)).map(x=>g.names[x]),
      missing_sample:next.missing.map(x=>g.names[x]).sort().slice(0,30)};
  }
  function analyze(g,rootNames,groups){
    assert(new Set(rootNames).size===rootNames.length&&rootNames.length,"duplicate or empty roots");
    const roots=rootNames.map(n=>{const id=g.ids.get(n);assert(id!==undefined&&g.rows[id]?.project,"missing project root "+n);return id});
    const base=walk(g,roots),individual=[];
    const unique=new Map();
    for(const group of groups){for(const a of group.members)for(const b of group.members)if(a.name!==b.name&&a.module!==b.module){
      const key=JSON.stringify([a.name,b.name]);unique.set(key,{from:a.name,to:b.name,from_module:a.module,to_module:b.module});
    }}
    for(const p of unique.values())individual.push(plan(g,roots,[p],base));
    individual.sort((a,b)=>(b.union?.net_removed??-Infinity)-(a.union?.net_removed??-Infinity)||JSON.stringify(a.pairs).localeCompare(JSON.stringify(b.pairs)));
    // Greedy joint replay; accept only strict additional benefit. Recompute closure
    // rather than summing independent scores. Reject incomplete data as evidence.
    let chosen=[],joint=plan(g,roots,[],base);
    for(const r of individual){
      if(r.union?.status!=="reference_graph_model_only"||r.union.net_removed<=0)continue;
      const trial=plan(g,roots,[...chosen,...r.pairs],base);
      if(trial.union?.status==="reference_graph_model_only"&&trial.union.net_removed>joint.union.net_removed){
        chosen=trial.pairs;joint=trial;
      }
    }
    return {schema:1,measurement:"value-edge-counterfactual-not-kernel-validation",root_names:rootNames,
      graph_declarations:g.rows.reduce((n,r)=>n+(r?1:0),0),graph_referenced_names:g.names.length,
      baseline:{...delta(g,base,base,roots),reachable_all:base.seen.size,missing_sample:base.missing.map(x=>g.names[x]).sort().slice(0,30)},
      individual,joint,limitations:["References are sets, not Exprs or occurrence counts.","No definitional equality, proof typechecking, source import visibility or kernel certificate is established.","External callers and type/kernel edges are not rewritten.","Missing reachable references prevent a complete model; even complete exported references may omit implicit dependencies.","Greedy joint search is not a global optimality proof; metrics are counterfactual only."]};
  }
  function tests(){
    let n=0;function eq(a,b,m){assert(JSON.stringify(a)===JSON.stringify(b),m+": "+JSON.stringify(a)+" != "+JSON.stringify(b));n++}
    function mk(spec){const g=graph();for(const [name,value=[],type=[],kernel=[],project=true] of spec)g.add({record:"decl",name,module:name,kind:"thm",project,value,type,kernel});return g}
    function run(spec,pairs,roots=["R"]){const g=mk(spec);return plan(g,roots.map(x=>g.ids.get(x)),pairs.map(([from,to])=>({from,to})))}
    eq(run([["R",["A","B"]],["A",["X"]],["B",["X"]],["X"]],[["A","B"]]).union.net_removed,1,"shared dependency");
    eq(run([["R",["A"],["A"]],["A"],["B"]],[["A","B"]]).union.net_removed,-1,"type edge remains");
    eq(run([["R",["A"],[],["A"]],["A"],["B"]],[["A","B"]]).victims_still_live,["A"],"kernel edge remains");
    eq(run([["R",["A"]],["A"],["B",["R"]]],[["A","B"]]).status,"new_dependency_cycle","reject cycle");
    eq(run([["R",["A"]],["A"],["B",["A"]]],[["A","B"]]).status,"new_dependency_cycle","reject recursive replacement");
    eq(run([["R",["A","B"]],["A"],["B"]],[["R","B"]]).status,"invalid_endpoint","protected root");
    eq(run([["R",["A"]],["A"],["B"]],[["A","Z"]]).status,"unknown_endpoint","missing replacement");
    eq(run([["R",["A"]],["A",["unknown"]],["B"]],[["A","B"]]).union.status,"incomplete_reference_graph","missing ref blocks evidence");
    eq(run([["R",["E"]],["A"],["B"],["E",["A"],[],[],false]],[["A","B"]]).union.net_removed,0,"external caller unchanged");
    eq(run([["R",["A","B"]],["A",["X"]],["B",["X"]],["C"],["D"],["X"]],[["A","C"],["B","D"]]).union.net_removed,1,"joint shared dependency disappears");
    eq(run([["R",["A"]],["A"],["B"],["C"]],[["A","B"],["B","C"]]).status,"chained_or_cyclic_aliases_unsupported","no alias chain");
    eq(run([["R",["A"]],["S",["B"]],["A"],["B"]],[["A","B"]],["R","S"]).per_root.R.net_removed,0,"per-root distinct from union");
    eq(run([["R"],["A"],["B"]],[["A","B"]]).union.net_removed,0,"dead code no gain");
    // Exhaustively check the model against an independent literal-set traversal
    // on 256 DAGs with old and new endpoints and protected type edges.
    for(let mask=0;mask<256;mask++){
      const bit=i=>Boolean(mask&(1<<i));
      const spec=[["R",["A",...(bit(0)?["B"]:[]),...(bit(1)?["X"]:[])],bit(2)?["A"]:[]],
        ["A",bit(3)?["X"]:[]],["B",bit(4)?["X"]:[],bit(5)?["Y"]:[]],["X",bit(6)?["Y"]:[]],["Y",[],[],[],!bit(7)]];
      const raw=new Map(spec.map(([name,value=[],type=[],kernel=[],project=true])=>[name,{value,type,kernel,project}]));
      function reference(change){const seen=new Set();function dfs(x){if(seen.has(x))return;seen.add(x);const r=raw.get(x);for(const d of [...r.type,...r.kernel,...r.value.map(y=>change&&r.project&&y==="A"?"B":y)])dfs(d)}dfs("R");return [...seen].filter(x=>x!=="R"&&raw.get(x).project).length}
      eq(run(spec,[["A","B"]]).union.net_removed,reference(false)-reference(true),"oracle DAG "+mask);
    }
    const g=mk([["R",["A","B"]],["A"],["B"]]);const result=analyze(g,["R"],[{members:[{name:"A",module:"A"},{name:"B",module:"B"}]}]);
    eq(result.individual.length,2,"both directions");eq(result.joint.union.net_removed,1,"joint choice");
    return n;
  }
  return {ROOTS,graph,walk,plan,analyze,tests};
}
async function cli(){
  const fs=require("node:fs"),zlib=require("node:zlib"),crypto=require("node:crypto"),readline=require("node:readline");
  const api=proofopt(),args=process.argv.slice(2);
  if(args[0]==="--self-test"){console.log(`PASS ${api.tests()} assertions`);return}
  if(args.length!==4)throw Error("usage: node closure_counterfactual.cjs GRAPH.gz SHA256 ROUND12.json OUTPUT.json");
  const [graphPath,expected,censusPath,out]=args;
  const g=api.graph(),digest=crypto.createHash("sha256");
  const stream=fs.createReadStream(graphPath).pipe(zlib.createGunzip());
  stream.on("data",c=>digest.update(c));
  let header=false;
  for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
    const r=JSON.parse(line);
    if(!header){if(r.schema!==1||r.record!=="header"||r.measurement!=="kernel-reference-graph")throw Error("bad graph header");header=true}
    else g.add(r);
  }
  const actual=digest.digest("hex");if(!header||actual!==expected)throw Error("graph digest mismatch: "+actual);
  const census=JSON.parse(fs.readFileSync(censusPath,"utf8"));
  if(census.input.graph_sha256!==actual)throw Error("census graph digest mismatch");
  const result=api.analyze(g,api.ROOTS,census.census.candidates);
  if(result.graph_declarations!==census.census.declarations)throw Error("declaration count mismatch");
  result.input_sha256=actual;
  fs.writeFileSync(out,JSON.stringify(result,null,2)+"\n");
  console.log(JSON.stringify({baseline:result.baseline,candidates:result.individual.map(r=>({pairs:r.pairs,status:r.status,net_removed:r.union?.net_removed,live_callers:r.changed_live_callers})),joint:result.joint.union},null,2));
}
cli().catch(e=>{console.error(e);process.exitCode=1});
