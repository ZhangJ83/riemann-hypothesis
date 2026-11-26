'use strict';
function scopeEngine(){
  const ROOTS=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
  function check(ok,msg){if(!ok)throw new Error(msg)}
  function createGraph(){
    const ids=new Map(),names=[],rows=[];
    function intern(name){
      check(typeof name==="string"&&name.length&&!/[\r\n\t]/.test(name),"invalid name");
      if(!ids.has(name)){ids.set(name,names.length);names.push(name)}
      return ids.get(name);
    }
    function add(r){
      check(r.record==="decl"&&typeof r.project==="boolean","invalid row");
      const id=intern(r.name);check(!rows[id],"duplicate name: "+r.name);
      for(const k of ["type","value","kernel"])check(Array.isArray(r[k]),"missing "+k);
      rows[id]={project:r.project,deps:[...new Set([...r.type,...r.value,...r.kernel].map(intern))]};
    }
    return {ids,names,rows,add};
  }
  function closure(g,roots){
    check(roots.length>0&&roots.length<=10&&new Set(roots).size===roots.length,"invalid roots");
    const mask=new Uint16Array(g.names.length),rootIds=roots.map(name=>{
      const i=g.ids.get(name);check(i!==undefined&&g.rows[i]?.project,"missing project root: "+name);return i;
    });
    const rootSet=new Set(rootIds),perRoot=[];
    for(let i=0;i<roots.length;i++){
      const bit=1<<i,stack=[rootIds[i]];
      let all=0,project=0;
      while(stack.length){
        const id=stack.pop();if(mask[id]&bit)continue;
        const row=g.rows[id];check(row,"unresolved reachable reference: "+g.names[id]);
        mask[id]|=bit;all++;if(row.project)project++;
        for(const dep of row.deps)if(!(mask[dep]&bit))stack.push(dep);
      }
      perRoot.push({name:roots[i],all,project_including_root:project});
    }
    let union=0,project=0,withoutRoots=0;
    for(let i=0;i<mask.length;i++)if(mask[i]){
      union++;
      if(g.rows[i].project){project++;if(!rootSet.has(i))withoutRoots++}
    }
    return {mask,summary:{declarations:g.rows.reduce((n,x)=>n+Number(Boolean(x)),0),
      root_names:roots,per_root:perRoot,union_all:union,union_project_including_roots:project,
      union_project_excluding_roots:withoutRoots}};
  }
  function tests(){
    let assertions=0;
    const eq=(a,b,msg)=>{check(JSON.stringify(a)===JSON.stringify(b),msg);assertions++};
    const throws=(fn,msg)=>{let threw=false;try{fn()}catch(e){threw=true}check(threw,msg);assertions++};
    function build(spec){const g=createGraph();for(const [name,project,type=[],value=[],kernel=[]] of spec)g.add({record:"decl",name,project,type,value,kernel});return g}
    const example=build([["R",true,["A"],["B"],["C"]],["S",true,[],["B"]],["A",true],["B",false,[],["A"]],["C",true,[],["R"]]]);
    let v=closure(example,["R","S"]);
    eq(v.summary.union_all,5,"union");eq(v.summary.union_project_excluding_roots,2,"project excluding roots");
    eq(v.mask[example.ids.get("A")],3,"shared");eq(v.mask[example.ids.get("C")],1,"kernel");
    throws(()=>closure(build([["R",true,[],["missing"]]]),["R"]),"missing ref fails");
    throws(()=>closure(example,["R","R"]),"duplicate root fails");
    throws(()=>example.add({record:"decl",name:"R",project:true,type:[],value:[],kernel:[]}),"duplicate row fails");
    throws(()=>build([["R\tS",true]]),"TSV injection fails");
    for(let s=0;s<256;s++){
      const spec=[["R",true,["A"],(s&1)?["B"]:[],(s&2)?["S"]:[]],
        ["S",true,[],["B"],(s&4)?["R"]:[]],["A",true,[],(s&8)?["B"]:[],(s&16)?["C"]:[]],
        ["B",false,(s&32)?["C"]:[],[],(s&64)?["A"]:[]],["C",Boolean(s&128),[],["C"]]];
      const g=build(spec);const out=closure(g,["R","S"]);const byName=new Map(spec.map(x=>[x[0],x]));
      const sets=["R","S"].map(root=>{const set=new Set();function walk(n){if(set.has(n))return;set.add(n);for(const x of byName.get(n).slice(2).flat())walk(x)}walk(root);return set});
      for(const n of byName.keys())eq(out.mask[g.ids.get(n)],(sets[0].has(n)?1:0)+(sets[1].has(n)?2:0),"oracle mask "+s+" "+n);
      const union=new Set([...sets[0],...sets[1]]);
      eq(out.summary.union_project_excluding_roots,[...union].filter(n=>n!=="R"&&n!=="S"&&byName.get(n)[1]).length,"oracle project "+s);
    }
    return assertions;
  }
  return {ROOTS,createGraph,closure,check,tests};
}
async function main(){
  const fs=require("node:fs"),zlib=require("node:zlib"),crypto=require("node:crypto"),readline=require("node:readline"),path=require("node:path");
  const api=scopeEngine(),args=process.argv.slice(2);
  if(args[0]==="--self-test"){console.log("PASS "+api.tests()+" assertions");return}
  if(args.length!==3)throw Error("usage: node dag_scope.cjs GRAPH.jsonl.gz EXPECTED_SHA256 OUTPUT_DIR");
  const [graphFile,expected,dir]=args,g=api.createGraph(),h=crypto.createHash("sha256");
  const stream=fs.createReadStream(graphFile).pipe(zlib.createGunzip());stream.on("data",b=>h.update(b));
  let header=null;
  for await(const line of readline.createInterface({input:stream,crlfDelay:Infinity})){
    const row=JSON.parse(line);
    if(!header){api.check(row.record==="header"&&row.schema===1&&row.measurement==="kernel-reference-graph","invalid header");header=row}
    else g.add(row);
  }
  const actual=h.digest("hex");api.check(header&&actual===expected,"graph digest mismatch");
  api.check(JSON.stringify(header.roots)===JSON.stringify(api.ROOTS),"root order mismatch");
  const {mask,summary}=api.closure(g,api.ROOTS);
  fs.mkdirSync(dir,{recursive:true});
  const lines=[];
  for(let i=0;i<mask.length;i++)if(mask[i])lines.push(g.names[i]+"\t"+mask[i]+"\t"+Number(g.rows[i].project));
  lines.sort();
  fs.writeFileSync(path.join(dir,"scope.tsv"),lines.join("\n")+"\n");
  summary.input_sha256=actual;summary.scope_sha256=crypto.createHash("sha256").update(fs.readFileSync(path.join(dir,"scope.tsv"))).digest("hex");
  fs.writeFileSync(path.join(dir,"scope.json"),JSON.stringify(summary,null,2)+"\n");
  console.log(JSON.stringify(summary));
}
main().catch(e=>{console.error(e);process.exitCode=1});
