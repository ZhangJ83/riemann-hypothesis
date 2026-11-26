"use strict";
function selectPairs(report, limit=100){
  if(!Number.isSafeInteger(limit)||limit<1||limit>100)throw Error("bad limit");
  if(!report||report.schema!==1||!Array.isArray(report.candidates)||report.candidates.length>100)throw Error("bad report");
  const safe=s=>typeof s==="string"&&s.length<=512&&/^[A-Za-z_][A-Za-z0-9_'.]*$/.test(s)&&!s.includes("..")&&!s.endsWith(".");
  const seen=new Set, pairs=[];let invalid=0,duplicate=0,within=0;
  for(const c of report.candidates){
    if(!c||!c.left||!c.right||!c.result||c.result.ok!==true||c.result.kernelChecked!==false||!safe(c.left.name)||!safe(c.right.name)||c.left.name===c.right.name||typeof c.left.module!=="string"||typeof c.right.module!=="string"){invalid++;continue}
    if(c.left.module===c.right.module){within++;continue}
    const a=c.left.name,b=c.right.name,k=JSON.stringify([a,b].sort());
    if(seen.has(k)){duplicate++;continue}seen.add(k);pairs.push([a,b]);
  }
  return {pairs:pairs.slice(0,limit),invalid,duplicate,within,omitted:Math.max(0,pairs.length-limit)};
}

function driver(pairs,core){
  return "import Main\n"+core+"\n"+pairs.map(([a,b])=>"#proofopt_probe "+JSON.stringify(a)+" "+JSON.stringify(b)).join("\n")+"\n";
}

function selfTest(){
  let n=0;const ok=(x)=>{if(!x)throw Error("self-test failed at "+n);n++};
  const c=(a,b,m="A",k="B")=>({left:{name:a,module:m},right:{name:b,module:k},result:{ok:true,kernelChecked:false}});
  for(let i=1;i<=100;i++){
    const rows=Array.from({length:i},(_,j)=>c("M.a"+j,"N.b"+j));
    const report={schema:1,candidates:rows};
    const x=selectPairs(report,Math.min(i,17));ok(x.pairs.length===Math.min(i,17));ok(x.omitted===Math.max(0,i-17));
    ok(driver(x.pairs,"import Lean\n").split("#proofopt_probe ").length===x.pairs.length+1);
  }
  const x=selectPairs({schema:1,candidates:[c("A.a","B.b"),c("B.b","A.a"),c("A.a","A.c","A","A"),c("A.a\n#eval 1","B.b"),c("A.a","A.a"),{...c("A.x","B.y"),result:{ok:true,kernelChecked:true}}]});
  ok(x.pairs.length===1);ok(x.invalid===3);ok(x.duplicate===1);ok(x.within===1);
  for(const bad of [null,{schema:2,candidates:[]},{schema:1,candidates:Array(101).fill(null)}]){let rejected=false;try{selectPairs(bad)}catch{rejected=true}ok(rejected)}
  return n;
}
if(require.main===module){
  const fs=require("node:fs");
  if(process.argv[2]==="--self-test"){console.log("PASS "+selfTest()+" driver assertions");process.exit(0)}
  const [,,input,corePath,outPath,manifestPath]=process.argv;
  if(!manifestPath)throw Error("usage: typed_driver.cjs REPORT CORE OUT MANIFEST");
  const selected=selectPairs(JSON.parse(fs.readFileSync(input,"utf8")));
  if(!selected.pairs.length)throw Error("no eligible pairs");
  fs.writeFileSync(outPath,driver(selected.pairs,fs.readFileSync(corePath,"utf8")));
  fs.writeFileSync(manifestPath,JSON.stringify(selected,null,2)+"\n");
}
module.exports={selectPairs,driver,selfTest};
