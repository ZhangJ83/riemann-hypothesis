'use strict';
function locCore(){
  const ROOTS=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
  const need=(x,m)=>{if(!x)throw Error(m)};
  function scope(raw,summary,roots=ROOTS){
    need(JSON.stringify(summary.root_names)===JSON.stringify(roots),"root drift");
    const map=new Map();
    for(const line of raw.trimEnd().split("\n")){
      const p=line.split("\t"),[name,mask,project]=p;
      need(p.length===3&&name&&!map.has(name)&&/^[0-9]+$/.test(mask)&&Number(mask)>0&&Number(mask)<2**roots.length&&["0","1"].includes(project),"invalid scope row: "+line);
      map.set(name,{mask:Number(mask),project:project==="1"});
    }
    need(map.size===summary.union_all,"scope size drift");
    let owned=0;for(const v of map.values())if(v.project)owned++;
    need(owned===summary.union_project_including_roots,"scope ownership drift");
    roots.forEach((r,i)=>need(map.get(r)?.project&&(map.get(r).mask&(1<<i)),"missing root "+r));
    return map;
  }
  function inventory(modules){
    const by=new Map();
    for(const {module,path} of modules){
      need(typeof module==="string"&&module&&typeof path==="string"&&path.startsWith("src/")&&path.endsWith(".lean")&&path.split("/").every(s=>s&&s!=="."&&s!=="..")&&path.slice(4,-5).replaceAll("/",".")===module&&!by.has(module),"invalid module inventory "+module);
      by.set(module,path);
    }
    return by;
  }
  function census(map,modules,summary,roots=ROOTS){
    const seen=new Set(),owned=new Map();let rows=0,header=false;
    function consume(r){
      if(!header){need(r.record==="header"&&r.schema===1&&r.measurement==="kernel-reference-graph"&&JSON.stringify(r.roots)===JSON.stringify(roots),"bad graph header");header=true;return}
      need(r.record==="decl"&&typeof r.name==="string","bad declaration record");rows++;
      const s=map.get(r.name);if(!s)return;
      need(!seen.has(r.name)&&s.project===r.project,"scope/graph row mismatch "+r.name);seen.add(r.name);
      if(s.project){need(modules.has(r.module),"project declaration has no audited module "+r.module);owned.set(r.module,(owned.get(r.module)||0)+1)}
    }
    function finish(){
      need(header&&rows===summary.declarations&&seen.size===map.size,"incomplete graph census");
      return [...owned].sort((a,b)=>a[0].localeCompare(b[0])).map(([module,reachable_declarations])=>({module,path:modules.get(module),reachable_declarations}));
    }
    return {consume,finish};
  }
  // Lexical line proxy, not parser-certified declaration spans; nested comments and escaped strings.
  function codeLineCount(text){
    let count=0,block=0,string=false,escaped=false;
    for(const line of text.split(/\r?\n/)){
      let has=false;
      for(let i=0;i<line.length;i++){
        const a=line[i],b=line[i+1];
        if(block){if(a==="/"&&b==="-"){block++;i++}else if(a==="-"&&b==="/"){block--;i++}continue}
        if(string){has=true;if(escaped)escaped=false;else if(a==="\\")escaped=true;else if(a==='"')string=false;continue}
        if(a==="-"&&b==="-")break;
        if(a==="/"&&b==="-"){block++;i++;continue}
        if(a==='"'){string=true;has=true;continue}
        if(!/\s/.test(a))has=true;
      }
      if(has)count++;
    }
    need(block===0,"unterminated Lean comment");return count;
  }
  function tests(){
    let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"test failed "+JSON.stringify([a,b]));n++};
    const fail=f=>{let ok=false;try{f()}catch{ok=true}eq(ok,true)};
    const roots=["R","S"],raw="R\t1\t1\nS\t2\t1\nP\t3\t1\nX\t3\t0\n",summary={root_names:roots,union_all:4,union_project_including_roots:3,declarations:5};
    const s=scope(raw,summary,roots),m=inventory([{module:"Main",path:"src/Main.lean"},{module:"Lib.A",path:"src/Lib/A.lean"}]);
    const header={record:"header",schema:1,measurement:"kernel-reference-graph",roots},row=(name,module,project)=>({record:"decl",name,module,project});
    const input=[header,row("R","Main",true),row("S","Main",true),row("P","Lib.A",true),row("X","Mathlib",false),row("Dead","Lib.A",true)];
    function run(rows){const c=census(s,m,summary,roots);rows.forEach(c.consume);return c.finish()}
    eq(run(input),[{module:"Lib.A",path:"src/Lib/A.lean",reachable_declarations:1},{module:"Main",path:"src/Main.lean",reachable_declarations:2}]);
    fail(()=>run(input.slice(0,-1)));fail(()=>run([...input.slice(0,-1),input[1]]));fail(()=>run([header,...input.slice(1,3),row("P","Missing",true),...input.slice(4)]));fail(()=>run([header,...input.slice(1,3),row("P","Lib.A",false),...input.slice(4)]));
    fail(()=>scope(raw,{...summary,union_all:5},roots));fail(()=>scope(raw+"P\t3\t1\n",summary,roots));fail(()=>scope(raw.replace("P\t3","P\t4"),summary,roots));fail(()=>inventory([{module:"../bad",path:"src/../bad.lean"}]));
    eq(codeLineCount("a := 1\n\n-- comment\nb := 2"),2);
    eq(codeLineCount("a := 1 /- x\n/- nested -/\n-/ b := 2"),2);
    eq(codeLineCount('x := " -- not comment "\ny := "\\\"/-"'),2);
    eq(codeLineCount("/- comment -/"),0);fail(()=>codeLineCount("a := 1\n/- open"));
    return n;
  }
  return {ROOTS,scope,inventory,census,codeLineCount,tests};
}

const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto"),zlib=require("node:zlib"),readline=require("node:readline");
const api=locCore(),args=process.argv.slice(2);
async function main(){
  if(args[0]==="--self-test"){console.log("PASS "+api.tests()+" assertions");return}
  if(args.length!==6)throw Error("usage: scoped_loc.cjs GRAPH.gz SCOPE_DIR SNAPSHOT.json before|after SOURCE_ROOT REPORT.json");
  const [graph,dir,snap,side,repo,out]=args;
  if(!["before","after"].includes(side))throw Error("bad side");
  const snapshot=JSON.parse(fs.readFileSync(snap,"utf8")),summary=JSON.parse(fs.readFileSync(path.join(dir,"scope.json"),"utf8"));
  const raw=fs.readFileSync(path.join(dir,"scope.tsv"));
  if(crypto.createHash("sha256").update(raw).digest("hex")!==summary.scope_sha256)throw Error("scope hash mismatch");
  const inv=api.inventory(snapshot[side==="before"?"reference":"current"].modules);
  const map=api.scope(raw.toString("utf8"),summary),c=api.census(map,inv,summary);
  const stream=fs.createReadStream(graph).pipe(zlib.createGunzip()),hash=crypto.createHash("sha256");stream.on("data",b=>hash.update(b));
  for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity}))c.consume(JSON.parse(line));
  if(hash.digest("hex")!==summary.input_sha256)throw Error("graph hash mismatch");
  const files=c.finish().map(x=>({...x,nonblank_noncomment_lines:api.codeLineCount(fs.readFileSync(path.join(repo,x.path),"utf8"))}));
  const report={schema:1,measurement:"reachable project module lexical LOC upper-bound proxy",commit:side==="before"?snapshot.base:snapshot.head,input_sha256:summary.input_sha256,scope_sha256:summary.scope_sha256,roots:api.ROOTS,reachable_declarations:map.size,reachable_project_modules:files.length,project_owned_nonblank_noncomment_loc_proxy:files.reduce((s,x)=>s+x.nonblank_noncomment_lines,0),target_loc:2000,scope_note:"Counts whole files containing reachable project declarations, not exact declaration spans; lexical comments/strings only; excludes external Mathlib/TauCeti. Do not treat as flagship dependency/DAG/CPU reduction.",files};
  fs.writeFileSync(out,JSON.stringify(report,null,2)+"\n");
  const {files:ignored,...small}=report;console.log(JSON.stringify(small));
}
main().catch(e=>{console.error(e);process.exitCode=1});
