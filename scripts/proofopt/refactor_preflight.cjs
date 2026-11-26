'use strict';
function preflightCore(){
  const approved=["src/Lib/General/Groups/CongruenceSubgroups.lean","src/Lib/Weil/Fock/Basic.lean","src/New/Appendix/DiscreteSeries/Localization.lean","src/New/Determinant/Exchange/NegativeIndices.lean"];
  const need=(x,m)=>{if(!x)throw Error(m)};
  const old=/\b(?:New\.)?(?:Fock|DiscreteSeries)\.conjTranspose_signMatrix\b/;
  function plan(snapshot){
    const p=snapshot?.diff?.changed;
    need(Array.isArray(p)&&p.length===approved.length&&new Set(p).size===p.length&&approved.every(x=>p.includes(x)),"approved source set mismatch");
    need(snapshot.base==="2746005d8130ee6d0c82d771ec11d69521a65093","historical base mismatch");
    return approved.map(path=>({path,module:path.slice(4,-5).replaceAll("/","."),stem:path.slice(4,-5)}));
  }
  function audit(sources){
    need(sources.size===approved.length&&approved.every(p=>sources.has(p)),"source set mismatch");
    let declarations=0, references=0;
    for(const [path,src] of sources){
      need(typeof src==="string"&&!old.test(src),"obsolete qualified theorem: "+path);
      const n=(src.match(/^\s*(?:lemma|theorem)\s+conjTranspose_signMatrix\b/gm)||[]).length;
      need(n===(path===approved[0]?1:0),"canonical declaration in wrong file or duplicated: "+path);
      declarations+=n;
      if(path!==approved[0]){
        const k=(src.match(/\bNew\.conjTranspose_signMatrix\b/g)||[]).length;
        need(k>=1,"consumer lacks explicit canonical reference: "+path);
        references+=k;
      }
    }
    return {declarations,references};
  }
  function matched(relative,modules){
    need(typeof relative==="string"&&!relative.startsWith("/")&&!relative.split("/").some(p=>p===".."||p==="."),"unsafe artifact path");
    return modules.some(({stem})=>{
      const i=("/"+relative).lastIndexOf("/"+stem+".");
      if(i<0)return false;
      const suffix=("/"+relative).slice(i+stem.length+2);
      return suffix.length>0&&!suffix.includes("/");
    });
  }
  function tests(){
    let n=0;const eq=(a,b)=>{need(JSON.stringify(a)===JSON.stringify(b),"test failed "+JSON.stringify([a,b]));n++};
    const fails=f=>{let x=false;try{f()}catch{x=true}eq(x,true)};
    const snapshot={base:"2746005d8130ee6d0c82d771ec11d69521a65093",diff:{changed:[...approved].reverse()}};
    const p=plan(snapshot);
    eq(p.length,4);eq(p[0].module,"Lib.General.Groups.CongruenceSubgroups");eq(p[3].module,"New.Determinant.Exchange.NegativeIndices");
    fails(()=>plan({...snapshot,base:"wrong"}));fails(()=>plan({...snapshot,diff:{changed:approved.slice(0,3)}}));fails(()=>plan({...snapshot,diff:{changed:[approved[0],approved[0],...approved.slice(2)]}}));
    const src=new Map(approved.map((x,i)=>[x,i===0?"lemma conjTranspose_signMatrix : True := by trivial":"exact New.conjTranspose_signMatrix"]));
    eq(audit(src),{declarations:1,references:3});
    for(const bad of ["exact Fock.conjTranspose_signMatrix","exact New.Fock.conjTranspose_signMatrix","exact DiscreteSeries.conjTranspose_signMatrix","exact New.DiscreteSeries.conjTranspose_signMatrix","exact unrelated"]){
      const s=new Map(src);s.set(approved[3],bad);fails(()=>audit(s));
    }
    const dup=new Map(src);dup.set(approved[1],"lemma conjTranspose_signMatrix : True := by trivial\nexact New.conjTranspose_signMatrix");fails(()=>audit(dup));
    for(const {stem} of p)for(const root of ["lib/lean","ir","nested/lib/lean"])for(const suffix of ["olean","olean.private","olean.server","ilean","trace","c","c.o","hash"]){
      eq(matched(root+"/"+stem+"."+suffix,p),true);
      eq(matched(root+"/"+stem+"Other."+suffix,p),false);
      eq(matched(root+"/"+stem+"/Nested."+suffix,p),false);
      eq(matched(root+"/"+stem+".dir/Nested."+suffix,p),false);
    }
    fails(()=>matched("../bad",p));fails(()=>matched("/bad",p));
    return n;
  }
  return {plan,audit,matched,tests};
}

const fs=require("node:fs"),path=require("node:path"),cp=require("node:child_process");
const api=preflightCore(),[mode,filename,buildDir,reportFile]=process.argv.slice(2);
function main(){
  if(mode==="--self-test"){console.log("PASS "+api.tests()+" assertions");return}
  if(!filename)throw Error("usage: --audit SNAPSHOT | --targets SNAPSHOT | --prune SNAPSHOT BUILD REPORT");
  const plan=api.plan(JSON.parse(fs.readFileSync(filename,"utf8")));
  if(mode==="--targets"){for(const p of plan)console.log("+"+p.module);return}
  if(mode==="--audit"){
    const report=api.audit(new Map(plan.map(p=>[p.path,fs.readFileSync(p.path,"utf8")])));
    // Git grep checks every tracked Lean source, including consumers outside these four files.
    const scan=cp.spawnSync("git",["grep","-nE","(New[.])?(Fock|DiscreteSeries)[.]conjTranspose_signMatrix","--","src"],{encoding:"utf8"});
    if(scan.status!==1)throw Error("obsolete reference or grep failure: "+scan.status+"\n"+scan.stdout+"\n"+scan.stderr);
    const decl=cp.execFileSync("git",["grep","-nE","^[[:space:]]*(lemma|theorem)[[:space:]]+conjTranspose_signMatrix([[:space:]]|$)","--","src"],{encoding:"utf8"}).trim().split("\n");
    if(decl.length!==1||!decl[0].startsWith(plan[0].path+":"))throw Error("canonical declaration census failed: "+decl.join("\n"));
    console.log(JSON.stringify({...report,modules:plan.map(p=>p.module)}));return;
  }
  if(mode!=="--prune"||!buildDir||!reportFile)throw Error("invalid arguments");
  const root=path.resolve(buildDir),deleted=[];
  if(fs.lstatSync(root).isSymbolicLink())throw Error("symlink build root");
  function scan(dir,remove){
    for(const e of fs.readdirSync(dir,{withFileTypes:true})){
      const full=path.join(dir,e.name),rel=path.relative(root,full).split(path.sep).join("/");
      if(e.isDirectory()){scan(full,remove);continue}
      if(!api.matched(rel,plan))continue;
      if(!e.isFile())throw Error("nonregular matched artifact: "+rel);
      if(!remove)throw Error("stale artifact survived: "+rel);
      fs.unlinkSync(full);deleted.push(rel);
    }
  }
  scan(root,true);scan(root,false);
  fs.writeFileSync(reportFile,JSON.stringify({schema:1,modules:plan.map(p=>p.module),deleted:deleted.sort(),remaining:0},null,2)+"\n");
  console.log("invalidated "+deleted.length+" artifacts across all "+plan.length+" approved modules");
}
try{main()}catch(e){console.error(e);process.exitCode=1}
