function makeCore(){
 const roots=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
 const required=["Challenge.lean","comparator.json","src/Main.lean","src/Statements.lean","lakefile.toml","lake-manifest.json","lean-toolchain"];
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
 function parseTree(raw){
  return raw.split("\0").filter(Boolean).map(line=>{
   const m=/^([0-7]+) (blob|tree|commit) ([0-9a-f]{40})\t([\s\S]+)$/.exec(line);
   assert(m,"invalid ls-tree record");return {mode:m[1],type:m[2],sha:m[3],path:m[4]};
  });
 }
 function inventory(tree, comparator, manifest, lean){
  assert(Array.isArray(tree),"tree required");
  const by=new Map();
  for(const e of tree){
   assert(!by.has(e.path),"duplicate tree path "+e.path);
   assert(typeof e.path==="string"&&!e.path.startsWith("/")&&!e.path.split("/").includes(".."),"invalid path");
   assert(/^[0-9a-f]{40}$/.test(e.sha),"invalid blob identity");
   by.set(e.path,e);
  }
  const files=tree.filter(e=>e.type==="blob");
  assert(required.every(p=>by.get(p)?.type==="blob"),"missing protected/config file");
  assert(eq([...comparator.theorem_names].sort(),[...roots].sort()),"five theorem roots changed");
  assert(comparator.challenge_module==="Challenge"&&comparator.solution_module==="Main","unexpected comparator modules");
  assert(eq([...comparator.permitted_axioms].sort(),["Classical.choice","Quot.sound","propext"].sort()),"unexpected permitted axioms");
  assert(comparator.enable_nanoda===true,"nanoda disabled");
  const packs=manifest.packages.filter(p=>["mathlib","TauCeti"].includes(p.name));
  assert(packs.length===2&&new Set(packs.map(p=>p.name)).size===2&&packs.every(p=>/^[0-9a-f]{40}$/.test(p.rev)),"missing immutable dependency pins");
  const modules=files.filter(e=>/^src\/.+\.lean$/.test(e.path)).map(e=>{
   assert(["100644","100755"].includes(e.mode),"Lean source not a regular file");
   return {module:e.path.slice(4,-5).replaceAll("/","."),path:e.path,sha:e.sha};
  }).sort((a,b)=>a.module.localeCompare(b.module,"en"));
  assert(modules.some(x=>x.module==="Main")&&modules.some(x=>x.module==="New.Main"),"readable main module missing");
  assert(new Set(modules.map(m=>m.module)).size===modules.length,"module name collision");
  const protectedFiles=files.filter(e=>required.includes(e.path)||e.path==="export-targets.txt"||e.path.startsWith("comparator/")||e.path==="src/Challenge.lean").map(e=>[e.path,e.sha]).sort((a,b)=>a[0].localeCompare(b[0],"en"));
  return {schema:1,roots:[...roots],lean:lean.trim(),dependencies:Object.fromEntries(packs.map(p=>[p.name,p.rev]).sort()),protectedFiles,modules,legacyExportTargets:by.has("export-targets.txt")};
 }
 function check(base,candidate,allowed=[]){
  assert(eq(base.roots,candidate.roots),"root drift");
  assert(base.lean===candidate.lean&&eq(base.dependencies,candidate.dependencies),"toolchain/dependency drift");
  assert(eq(base.protectedFiles,candidate.protectedFiles),"protected file drift");
  const old=new Map(base.modules.map(x=>[x.path,x.sha])),now=new Map(candidate.modules.map(x=>[x.path,x.sha]));
  const diff=[...new Set([...old.keys(),...now.keys()])].filter(p=>old.get(p)!==now.get(p)).sort();
  assert(diff.every(p=>allowed.includes(p)),"unexpected Lean source change: "+diff.filter(p=>!allowed.includes(p)).join(","));
  assert(allowed.every(p=>diff.includes(p)),"approved source change missing");
  return {changed:diff,sourceCount:candidate.modules.length,protectedCount:candidate.protectedFiles.length};
 }
 function cacheDecision(code){if(code===0)return "exact";if(code===4)return "baseline";throw Error("cache unavailable or failed: "+code)}
 return {parseTree,inventory,check,cacheDecision};
}
export {makeCore};
