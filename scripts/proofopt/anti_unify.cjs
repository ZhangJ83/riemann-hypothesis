"use strict";
const arities={"bvar":0,"sort":0,"const":0,"app":2,"lam":2,"forallE":2,"letE":3,"natLit":0,"strLit":0,"proj":1};
function invariant(ok,message){if(!ok)throw Error(message)}

class ExprDag {
  constructor(){this.nodes=new Map;this.index=new Map;this.roots=[];this.names=new Set}
  key(tag,atom,children){return JSON.stringify([tag,atom,children])}
  add(id,tag,atom,children){
    invariant(Number.isSafeInteger(id)&&id>=0&&!this.nodes.has(id),"invalid or duplicate node ID");
    invariant(Object.hasOwn(arities,tag)&&Array.isArray(children)&&children.length===arities[tag],"bad tag/arity");
    invariant(children.every(c=>Number.isSafeInteger(c)&&c<id&&this.nodes.has(c)),"non-topological or missing child");
    if(tag==="bvar")invariant(Number.isSafeInteger(atom)&&atom>=0&&atom<Number.MAX_SAFE_INTEGER,"invalid de Bruijn index");
    else if(tag==="const"||tag==="proj")invariant(Array.isArray(atom)&&atom.length===2&&typeof atom[0]==="string"&&(tag==="const"?Array.isArray(atom[1])&&atom[1].every(u=>typeof u==="string"):Number.isSafeInteger(atom[1])&&atom[1]>=0),"invalid name payload");
    else if(["sort","natLit","strLit"].includes(tag))invariant(typeof atom==="string"&&(tag!=="natLit"||/^(0|[1-9][0-9]*)$/.test(atom)),"invalid literal payload");
    else invariant(atom===null,"unexpected atom");
    let loose=tag==="bvar"?atom+1:0;
    for(let i=0;i<children.length;i++){
      const binds=(tag==="lam"||tag==="forallE")&&i===1||tag==="letE"&&i===2;
      loose=Math.max(loose,this.nodes.get(children[i]).loose-(binds?1:0));
    }
    const key=this.key(tag,atom,children);
    invariant(!this.index.has(key),"input not hash-consed");
    this.index.set(key,id);this.nodes.set(id,{id,tag,atom,children,loose});
  }
  addRoot(name,module,type,proof,levels){
    invariant(typeof name==="string"&&name.length>0&&!this.names.has(name)&&typeof module==="string"&&module.length>0&&Array.isArray(levels)&&levels.every(x=>typeof x==="string"),"invalid root");
    invariant(this.nodes.get(type)?.loose===0&&this.nodes.get(proof)?.loose===0,"root missing or open");
    this.roots.push({name,module,type,proof,levels});this.names.add(name);
  }
  ingest(row){
    invariant(Array.isArray(row),"invalid row");
    if(row[0]==="n"){invariant(row.length===5,"bad node row");this.add(...row.slice(1))}
    else if(row[0]==="r"){invariant(row.length===6,"bad root row");this.addRoot(...row.slice(1))}
    else throw Error("unknown row kind");
  }
}

function antiUnify(dag,left,right,opts={}){
  const maxDepth=opts.maxDepth??128,maxPairs=opts.maxPairs??20000,maxHoles=opts.maxHoles??8;
  invariant(Number.isInteger(maxDepth)&&maxDepth>0&&Number.isInteger(maxPairs)&&maxPairs>0&&Number.isInteger(maxHoles)&&maxHoles>=0,"invalid limits");
  if(JSON.stringify(left.levels)!==JSON.stringify(right.levels))return {ok:false,reason:"universe-parameters"};
  const templates=[],memo=new Map,index=new Map,holes=[],holeIndex=new Map;
  let visited=0,rigid=0,exact=0,reason=null;
  function intern(entry){
    const k=JSON.stringify(entry);if(index.has(k))return index.get(k);
    const i=templates.length;templates.push(entry);index.set(k,i);return i;
  }
  function reject(r){reason=r;return -1}
  function visit(a,b,depth){
    if(depth>maxDepth)return reject("depth-budget");
    const k=a+":"+b;if(memo.has(k))return memo.get(k);
    if(++visited>maxPairs)return reject("pair-budget");
    const x=dag.nodes.get(a),y=dag.nodes.get(b);invariant(x&&y,"missing pair node");
    let id;
    if(a===b){id=intern(["ref",a]);exact++}
    else if(x.tag===y.tag&&JSON.stringify(x.atom)===JSON.stringify(y.atom)){
      const children=[];
      for(let i=0;i<x.children.length;i++){const c=visit(x.children[i],y.children[i],depth+1);if(c<0)return -1;children.push(c)}
      id=intern(["node",x.tag,x.atom,children]);rigid++;
    }else{
      // Only closed mismatch terms: no variable capture under any binder.
      if(x.loose!==0||y.loose!==0)return reject("open-mismatch");
      let h=holeIndex.get(k);
      if(h===undefined){
        if(holes.length>=maxHoles)return reject("hole-budget");
        h=holes.length;holeIndex.set(k,h);holes.push([a,b]);
      }
      id=intern(["hole",h]);
    }
    memo.set(k,id);return id;
  }
  const type=visit(left.type,right.type,0);if(type<0)return {ok:false,reason};
  const proof=visit(left.proof,right.proof,0);if(proof<0)return {ok:false,reason};
  if(templates[proof][0]==="hole")return {ok:false,reason:"whole-proof-hole"};
  if(holes.length===0)return {ok:false,reason:"exact-duplicate"};
  if(rigid===0)return {ok:false,reason:"no-rigid-context"};
  // Reconstruct both original DAGs exactly, not just by hashes or printing.
  for(let side=0;side<2;side++){
    const ids=[];
    for(const t of templates){
      let id;
      if(t[0]==="ref")id=t[1];
      else if(t[0]==="hole")id=holes[t[1]][side];
      else id=dag.index.get(dag.key(t[1],t[2],t[3].map(c=>ids[c])));
      invariant(id!==undefined,"reconstruction missing node");ids.push(id);
    }
    const root=side===0?left:right;
    invariant(ids[type]===root.type&&ids[proof]===root.proof,"reconstruction mismatch");
  }
  const used=(root)=>{
    const seen=new Set,hs=new Set,stack=[root];
    while(stack.length){const id=stack.pop();if(seen.has(id))continue;seen.add(id);const t=templates[id];if(t[0]==="hole")hs.add(t[1]);else if(t[0]==="node")stack.push(...t[3])}
    return [...hs].sort((a,b)=>a-b);
  };
  return {ok:true,type,proof,templates,holes,typeHoles:used(type),proofHoles:used(proof),rigid,exact,visited,validation:"exact-syntax-reconstruction-only",kernelChecked:false};
}

function headSignature(dag,id){
  let depth=0,binders=[];
  while(depth++<128){
    const n=dag.nodes.get(id);
    if(n.tag==="app"){id=n.children[0];continue}
    if(n.tag==="lam"||n.tag==="forallE"){binders.push(n.tag);id=n.children[1];continue}
    if(n.tag==="letE"){binders.push(n.tag);id=n.children[2];continue}
    return JSON.stringify([binders,n.tag,n.atom]);
  }
  return null;
}

function discover(dag,opts={}){
  const window=opts.window??32,budget=opts.budget??100000,top=opts.top??100;
  invariant([window,budget,top].every(x=>Number.isSafeInteger(x)&&x>0),"invalid discovery limits");
  const groups=new Map;let skippedHead=0;
  for(const r of [...dag.roots].sort((a,b)=>a.name<b.name?-1:a.name>b.name?1:0)){
    const h=headSignature(dag,r.proof),t=headSignature(dag,r.type);
    if(h===null||t===null){skippedHead++;continue}
    const k=JSON.stringify([h,t,r.levels]);if(!groups.has(k))groups.set(k,[]);groups.get(k).push(r);
  }
  let attempts=0,accepted=0,withinModule=0,omittedByWindow=0,exhausted=false;
  const rejected={},candidates=[];
  function cmp(a,b){return b.result.rigid-a.result.rigid||a.result.holes.length-b.result.holes.length||b.result.exact-a.result.exact||(a.left.name<b.left.name?-1:a.left.name>b.left.name?1:a.right.name<b.right.name?-1:a.right.name>b.right.name?1:0)}
  for(const g of groups.values())for(let i=0;i<g.length;i++)omittedByWindow+=Math.max(0,g.length-i-1-window);
  outer:for(const g of groups.values()){
    for(let i=0;i<g.length;i++)for(let j=i+1;j<Math.min(g.length,i+1+window);j++){
      const left=g[i],right=g[j];
      if(left.module===right.module){withinModule++;continue}
      if(attempts===budget){exhausted=true;break outer}
      attempts++;
      const result=antiUnify(dag,left,right,opts);
      if(!result.ok){rejected[result.reason]=(rejected[result.reason]??0)+1;continue}
      accepted++;
      candidates.push({left,right,result});candidates.sort(cmp);if(candidates.length>top)candidates.pop();
    }
  }
  return {schema:1,measurement:"bounded-syntactic-candidate-discovery",nodes:dag.nodes.size,roots:dag.roots.length,groups:groups.size,skippedHead,attempts,accepted,withinModule,omittedByWindow,exhausted,rejected,candidates,limits:{window,budget,top,maxDepth:opts.maxDepth??128,maxPairs:opts.maxPairs??20000,maxHoles:opts.maxHoles??8},actualDependencyReduction:null,actualDagReduction:null,kernelVerified:0};
}

function selfTest(){
  let assertions=0;
  function check(ok,msg){invariant(ok,msg);assertions++}
  function throws(f){let caught=false;try{f()}catch{caught=true}check(caught,"expected rejection")}
  const d=new ExprDag;
  function n(t,a,c=[]){const k=d.key(t,a,c);if(d.index.has(k))return d.index.get(k);const id=d.nodes.size;d.add(id,t,a,c);return id}
  const k=n("const",["K",[]]),a=n("const",["A",[]]),b=n("const",["B",[]]),c=n("const",["C",[]]),t=n("sort","zero"),v0=n("bvar",0),v1=n("bvar",1);
  const app=(x,y)=>n("app",null,[x,y]),lam=(x,y)=>n("lam",null,[x,y]),pi=(x,y)=>n("forallE",null,[x,y]),letE=(x,y,z)=>n("letE",null,[x,y,z]);
  const root=(name,module,type,proof,levels=[])=>({name,module,type,proof,levels});
  const f=x=>app(app(k,x),x);
  let l=root("L","M1",t,f(a)),r=root("R","M2",t,f(b));
  let s=antiUnify(d,l,r);check(s.ok,"repeated closed hole");check(s.holes.length===1,"pair memo");check(s.proofHoles.length===1&&s.typeHoles.length===0,"hole provenance");check(s.kernelChecked===false,"not kernel");
  check(antiUnify(d,l,l).reason==="exact-duplicate","exact case");
  check(antiUnify(d,l,r,{maxHoles:0}).reason==="hole-budget","hole cap");
  check(antiUnify(d,l,r,{maxPairs:1}).reason==="pair-budget","pair cap");
  check(antiUnify(d,l,r,{maxDepth:1}).reason==="depth-budget","depth cap");
  check(antiUnify(d,l,{...r,levels:["u"]}).reason==="universe-parameters","universe guard");
  check(antiUnify(d,root("x","X",t,a),root("y","Y",t,b)).reason==="whole-proof-hole","whole proof reject");
  check(antiUnify(d,root("x","X",t,lam(t,app(k,v0))),root("y","Y",t,lam(t,app(k,a)))).reason==="open-mismatch","bound variable capture reject");
  check(d.nodes.get(lam(t,v0)).loose===0,"binder closes body");
  check(d.nodes.get(lam(v0,t)).loose===1,"binder does not close domain");
  check(d.nodes.get(pi(t,v1)).loose===1,"forall nested index");
  check(d.nodes.get(letE(t,v0,v0)).loose===1,"let value outside binder");
  check(d.nodes.get(letE(t,a,v0)).loose===0,"let body inside binder");
  s=antiUnify(d,root("x","X",app(k,a),f(a)),root("y","Y",app(k,b),f(b)));
  check(s.ok&&s.typeHoles[0]===s.proofHoles[0],"shared substitution between type and proof");
  throws(()=>d.add(d.nodes.size,"app",null,[999999,0]));
  throws(()=>d.add(d.nodes.size,"bvar",-1,[]));
  throws(()=>d.add(d.nodes.size,"app",null,[0]));
  throws(()=>d.add(d.nodes.size,"const",["K",[]],[]));
  throws(()=>d.add(d.nodes.size,"unknown",null,[]));
  throws(()=>d.addRoot("open","X",t,v0,[]));
  d.addRoot(l.name,l.module,l.type,l.proof,[]);d.addRoot(r.name,r.module,r.type,r.proof,[]);
  d.addRoot("Z","M2",t,f(c),[]);
  let report=discover(d,{window:1,top:1});check(report.attempts===1&&report.accepted===1&&report.omittedByWindow===1&&report.withinModule===1,"bounded deterministic discovery");
  report=discover(d,{window:3,budget:1});check(report.exhausted&&report.attempts===1,"global budget");
  throws(()=>d.addRoot("L","M1",t,f(a),[]));
  // Independent reconstruction oracle over generated closed mismatch patterns:
  // each skeleton has 1–4 ordered, possibly repeated pairs and both binder depths.
  for(let seed=0;seed<512;seed++){
    let x=k,y=k;const expected=new Set;
    const atoms=[a,b,c];
    for(let j=0;j<4;j++){
      const i=(seed>>(2*j))%3,h=(i+1+((seed>>(j+1))&1))%3;
      x=app(x,atoms[i]);y=app(y,atoms[h]);expected.add(atoms[i]+":"+atoms[h]);
    }
    if(seed&1){x=lam(t,x);y=lam(t,y)}
    if(seed&2){x=letE(t,a,x);y=letE(t,a,y)}
    const z=antiUnify(d,root("x","X",t,x),root("y","Y",t,y));
    check(z.ok,"generated reconstruction "+seed);
    check(z.holes.length===expected.size,"independent hole count "+seed);
    check(z.holes.every(h=>expected.has(h.join(":"))),"independent substitution "+seed);
  }
  return assertions;
}

async function main(){
  const fs=require("node:fs"), readline=require("node:readline");
  if(process.argv[2]==="--self-test"){console.log("PASS "+selfTest()+" anti-unification assertions");return}
  const [, , input, output]=process.argv;invariant(input&&output,"usage: anti_unify.cjs INPUT.jsonl OUTPUT.json");
  const dag=new ExprDag;let lines=0;
  for await(const line of readline.createInterface({input:fs.createReadStream(input),crlfDelay:Infinity})){
    invariant(line.length>0,"empty record");dag.ingest(JSON.parse(line));lines++;
    invariant(dag.nodes.size<=1500000&&dag.roots.length<=100000,"input budget exceeded");
  }
  invariant(dag.roots.length>0,"no roots exported");
  const report=discover(dag);report.inputRows=lines;fs.writeFileSync(output,JSON.stringify(report,null,2)+"\n");
  console.log("AU_SUMMARY "+JSON.stringify({...report,candidates:report.candidates.length}));
}
module.exports={ExprDag,antiUnify,discover,selfTest};
if(require.main===module)main().catch(e=>{console.error(e);process.exitCode=1});
