// Narrow experimental source candidate generator for the two named RH clump members.
// Not a Lean parser or verifier. Do not apply to an arbitrary module.
function makePass(){
 const ns="UpperTheory.LiteratureTheorems.";
 const openType="_root_."+ns+"OpenImageCondition";
 const first="TemperedProductOfSquareIntegrable", second="TopMainZj";
 const callersA=["algebraic_character_wd_of_open","gelfand_kazhdan_dual_of_open","zelevinsky_polynomial_ring_of_open","hecke_ladic_character_crystalline_of_open","hecke_ladic_character_above_of_open","greenberg_wiles_of_open","galois_cohomology_from_literature"].map(x=>ns+x);
 const callersB=["local_inputs_from_literature","automorphic_inputs_from_literature"].map(x=>"UpperTheory.One.Join."+x);
 const check=(v,m)=>{if(!v)throw Error(m)};
 const esc=s=>s.replace(/[.*+?^${}()|[\]\\]/g,"\\$&");
 const qualified=/^(?:_root_\.)?(?:[\p{L}_][\p{L}\p{N}_']*\.)+[\p{L}_][\p{L}\p{N}_']*$/u;
 const root=s=>s.startsWith("_root_.")?s:"_root_."+s;
 function section(src,suffix){
  const starts=[...src.matchAll(/^-- ===== clump member: (.+) =====$/gm)].filter(x=>x[1].endsWith("."+suffix));
  check(starts.length===1,`ambiguous/missing member ${suffix}`);
  const x=starts[0],start=x.index+x[0].length+1, marker=`-- ===== end clump member: ${x[1]} =====`,end=src.indexOf(marker,start);
  check(end>=start&&src.indexOf(marker,end+marker.length)===-1,"invalid seam");
  return {start,end,body:src.slice(start,end)};
 }
 function declarations(body){
  const heads=[...body.matchAll(/^theorem ([^\s]+) /gm)];
  return heads.map((h,i)=>{
   const start=h.index, end=heads[i+1]?.index??body.length;
   let raw=body.slice(start,end);
   const close=raw.search(/^end(?: |$)/m); if(close>=0)raw=raw.slice(0,close);
   const sep=raw.indexOf(" :=\n");
   check(sep>=0,`unexpected declaration layout ${h[1]}`);
   return {name:h[1],start,end:start+raw.length,header:raw.slice(0,sep+4),value:raw.slice(sep+4)};
  });
 }
 function candidates(ds){
  const out=new Map();
  for(const d of ds){
   const prefix=`theorem ${d.name} `;
   if(!d.name.startsWith(ns))continue;
   const m=d.header.slice(prefix.length).match(new RegExp("^\\((_?O) : "+esc(openType)+"\\) : (\\S+) :=\\n$"));
   const rhs=d.value.trim();
   if(m&&qualified.test(m[2])&&qualified.test(rhs)&&!rhs.startsWith(ns)&&!rhs.startsWith("_root_."+ns)){
    check(!out.has(d.name),"duplicate wrapper");
    out.set(d.name,{name:d.name,type:root(m[2]),rhs:root(rhs)});
   }
  }
  return out;
 }
 function rewrite(src){
  const a=section(src,first),b=section(src,second);check(a.end<b.start,"unexpected member order");
  const da=declarations(a.body),db=declarations(b.body),cs=candidates(da), edits=[], counts=new Map();
  for(const [s,ds,allowed] of [[a,da,callersA],[b,db,callersB]]){
   for(const name of allowed)check(ds.filter(d=>d.name===name).length===1,`missing expected caller ${name}`);
   for(const d of ds.filter(d=>allowed.includes(d.name))){
    check(d.header.includes(`(O : ${openType})`),`unexpected caller binder ${d.name}`);
    check(!/--|\/-|"|`/.test(d.value),`unsupported comment/string in ${d.name}`);
    let v=d.value;
    for(const c of cs.values()){
     const token=`_root_.${c.name} O`, pat=new RegExp("(?<![\\p{L}\\p{N}_'.])"+esc(token)+"(?![\\p{L}\\p{N}_'.])","gu");
     const occurrences=[...v.matchAll(pat)].length;
     if(!occurrences)continue;
     v=v.replace(pat,`(show ${c.type} from ${c.rhs})`);
     counts.set(c.name,(counts.get(c.name)??0)+occurrences);
     edits.push({caller:d.name,wrapper:c.name,occurrences});
    }
    if(v!==d.value){s.changes??=[];s.changes.push({start:d.start+d.header.length,end:d.end,value:v});}
   }
  }
  let result=src;
  for(const s of [b,a]){
   let body=s.body;
   for(const e of (s.changes??[]).reverse())body=body.slice(0,e.start)+e.value+body.slice(e.end);
   result=result.slice(0,s.start)+body+result.slice(s.end);
  }
  const after=[...declarations(section(result,first).body),...declarations(section(result,second).body)];
  const before=[...da,...db];
  check(JSON.stringify(before.map(x=>x.header))===JSON.stringify(after.map(x=>x.header)),"theorem header drift");
  for(const d of before.filter(d=>cs.has(d.name)))check(after.find(x=>x.name===d.name)?.value===d.value,"wrapper body drift");
  const countRefs=(s,n)=>[...s.matchAll(new RegExp("(?<![\\p{L}\\p{N}_'])"+esc(n)+"(?![\\p{L}\\p{N}_'])","gu"))].length;
  const wrappers=[...counts].map(([name,replaced])=>({name,replaced,remaining_text_occurrences_in_file:countRefs(result,name),before_text_occurrences_in_file:countRefs(src,name)}));
  return {source:result,report:{eligible_wrappers:cs.size,rewritten_callers:new Set(edits.map(x=>x.caller)).size,replaced_calls:edits.reduce((n,e)=>n+e.occurrences,0),affected_wrappers:counts.size,wrappers_with_only_declaration_text:wrappers.filter(x=>x.remaining_text_occurrences_in_file===1).length,wrappers,edits,scope:"two explicitly selected clump members; proof bodies only",kernel_verified:false}};
 }
 return {rewrite,section,declarations,candidates};
}
export {makePass};
