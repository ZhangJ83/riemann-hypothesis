'use strict';
// Compare independently exported, actual before/after kernel reference scopes.
// Never count deleted unreachable declarations; count added live declarations.
const ROOTS=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
const OLD=["New.Fock.conjTranspose_signMatrix","New.DiscreteSeries.conjTranspose_signMatrix"];
const NEW="New.conjTranspose_signMatrix";
function need(p,m){if(!p)throw Error(m)}
function parse(tsv,roots){
  const m=new Map(),limit=2**roots.length;
  for(const line of tsv.trimEnd().split("\n")){
    const parts=line.split("\t"),[name,raw,project]=parts,mask=Number(raw);
    need(parts.length===3&&name&&!m.has(name)&&/^[0-9]+$/.test(raw)&&Number.isSafeInteger(mask)&&mask>0&&mask<limit&&(project==="0"||project==="1"),"invalid scope row: "+line);
    m.set(name,{mask,project:project==="1"});
  }
  roots.forEach((r,i)=>need(m.get(r)?.project&&(m.get(r).mask&(1<<i)),"missing project root "+r));
  return m;
}
function summarize(m,roots){
  const all=new Set(roots);
  return {all:m.size,project:[...m].filter(([n,r])=>r.project&&!all.has(n)).length,
    per:roots.map((n,i)=>({name:n,all:[...m.values()].filter(r=>r.mask&(1<<i)).length,
      project:[...m].filter(([k,r])=>k!==n&&r.project&&(r.mask&(1<<i))).length}))};
}
function compare(a,b,roots=ROOTS,old=OLD,canonical=NEW){
  const rs=new Set(roots);
  for(const [n,r] of a)if(b.has(n))need(r.project===b.get(n).project,"project ownership changed: "+n);
  const subset=(m,bit)=>new Set([...m].filter(([n,r])=>r.project&&!rs.has(n)&&(!bit||(r.mask&bit))).map(x=>x[0]));
  function diff(x,y){const removed=[...x].filter(k=>!y.has(k)).sort(),added=[...y].filter(k=>!x.has(k)).sort();return {before:x.size,after:y.size,net_removed:x.size-y.size,removed,added}}
  const union=diff(subset(a,0),subset(b,0));
  const per=roots.map((name,i)=>({name,...diff(subset(a,1<<i),subset(b,1<<i))}));
  const liveBefore=old.filter(n=>a.has(n)),liveAfter=old.filter(n=>b.has(n));
  const expected=liveBefore.length>0&&liveAfter.length===0&&b.get(canonical)?.project===true;
  return {schema:1,measurement:"actual-exported-kernel-reference-closure",union,per_root:per,
    old_live_before:liveBefore,old_live_after:liveAfter,canonical_live_after:b.has(canonical),
    structural_target_met:expected,positive_union_gain:union.net_removed>0,
    all_root_project_sets_nonincreasing:per.every(r=>r.net_removed>=0),
    actual_dag_reduction:null,actual_cpu_reduction:null,flagship_baseline_comparison:false};
}
function tests(){
  let count=0; const eq=(x,y)=>{need(JSON.stringify(x)===JSON.stringify(y),"assert mismatch "+JSON.stringify([x,y]));count++};
  const fail=f=>{let yes=false;try{f()}catch{yes=true}eq(yes,true)};
  const roots=["R","S"],mk=(rows)=>parse(rows.map(r=>r.join("\t")).join("\n")+"\n",roots);
  const common=[["R",1,1],["S",2,1],["mathlib",3,0]];
  const a=mk([...common,["A",1,1],["B",2,1]]);
  const b=mk([...common,["C",3,1]]);
  const r=compare(a,b,roots,["A","B"],"C");
  eq(r.union.net_removed,1);eq(r.union.removed,["A","B"]);eq(r.union.added,["C"]);
  eq(r.per_root.map(x=>x.net_removed),[0,0]);eq(r.structural_target_met,true);
  eq(compare(mk(common),mk(common),roots,["A","B"],"C").positive_union_gain,false);
  eq(compare(a,mk([...common,["C",3,1],["D",3,1],["E",1,1]]),roots,["A","B"],"C").union.net_removed,-1);
  eq(compare(a,a,roots,["A","B"],"C").structural_target_met,false);
  fail(()=>mk([...common,["R",1,1]]));fail(()=>mk([...common,["X",4,1]]));
  fail(()=>mk([...common,["X",1.5,1]]));fail(()=>mk([...common,["X",1,2]]));fail(()=>mk([["S",2,1]]));
  fail(()=>compare(a,mk([...common,["A",1,0]]),roots,["A","B"],"C"));
  // Exhaustive masks for independently reachable A/B/C and a nuisance node.
  for(let i=0;i<256;i++){
    let rows=common.slice(), next=common.slice();
    for(const [k,mask,dst] of [["A",i&3,rows],["B",(i>>2)&3,rows],["C",(i>>4)&3,next],["D",(i>>6)&3,next]])if(mask)dst.push([k,mask,1]);
    const out=compare(mk(rows),mk(next),roots,["A","B"],"C");
    eq(out.union.net_removed,rows.length-next.length);
    for(let j=0;j<2;j++)eq(out.per_root[j].net_removed,rows.slice(3).filter(x=>x[1]&(1<<j)).length-next.slice(3).filter(x=>x[1]&(1<<j)).length);
  }
  return count;
}
async function cli(){
  const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
  const args=process.argv.slice(2);
  if(args[0]==="--self-test"){console.log("PASS "+tests()+" assertions");return}
  need(args.length===3,"usage: compare_refactor.cjs BEFORE_DIR AFTER_DIR OUT.json");
  const load=d=>{
    const s=JSON.parse(fs.readFileSync(path.join(d,"scope.json"),"utf8")),raw=fs.readFileSync(path.join(d,"scope.tsv"),"utf8");
    need(crypto.createHash("sha256").update(raw).digest("hex")===s.scope_sha256,"scope hash mismatch");
    need(JSON.stringify(s.root_names)===JSON.stringify(ROOTS),"root names changed");
    const m=parse(raw,ROOTS),t=summarize(m,ROOTS);
    need(t.all===s.union_all&&t.project===s.union_project_excluding_roots,"summary differs from scope");
    return {s,m};
  };
  const a=load(args[0]),b=load(args[1]),r=compare(a.m,b.m);
  need(a.s.input_sha256==="5a1f971e33e3c0449137327e7ed46ae4d8742c31e4c0e8449525005d03c5591c","unexpected historical graph");
  need(a.s.union_project_excluding_roots===49503&&a.s.union_all===220703,"historical count drift");
  r.before_graph_sha256=a.s.input_sha256;r.after_graph_sha256=b.s.input_sha256;
  fs.writeFileSync(args[2],JSON.stringify(r,null,2)+"\n");
  console.log(JSON.stringify(r));
  need(r.structural_target_met&&r.positive_union_gain&&r.all_root_project_sets_nonincreasing,"real refactor has not demonstrated positive, nonregressing closure gain");
}
if(typeof module!=="undefined")module.exports={parse,compare,tests};
if(typeof require!=="undefined"&&require.main===module)cli().catch(e=>{console.error(e);process.exitCode=1});
