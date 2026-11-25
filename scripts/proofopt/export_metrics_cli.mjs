import {createReadStream,readFileSync} from "node:fs";
import {createInterface} from "node:readline";
import {createHash} from "node:crypto";
import {lib} from "./export_metrics.mjs";
const ROOTS=["riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re","LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive"];
async function exportFile(file,shared){
 const stream=createReadStream(file),hash=createHash("sha256"),p=lib.parser(shared);
 stream.on("data",chunk=>hash.update(chunk));
 for await(const line of createInterface({input:stream,crlfDelay:Infinity}))p.line(line);
 return {snapshot:p.finish(),sha256:hash.digest("hex")};
}
async function ownership(file){
 if(file==="-")return {owners:null,sha256:null};
 const hash=createHash("sha256"),stream=createReadStream(file),rows=[];
 stream.on("data",chunk=>hash.update(chunk));
 for await(const line of createInterface({input:stream,crlfDelay:Infinity})){
  const r=JSON.parse(line);if(r.record!=="owner")throw Error("invalid ownership row");
  // Unclassified names are not assumed external. Reachable missing ownership fails.
  if(r.project!==null)rows.push(r);
 }
 return {owners:lib.owners(rows),sha256:hash.digest("hex")};
}
async function load(exp,own,pool){
 const a=await exportFile(exp,pool),b=await ownership(own);
 return {...a,...b,export_sha256:a.sha256,ownership_sha256:b.sha256};
}
const [mode,...args]=process.argv.slice(2);
try{
 const p=lib.pool();let out;
 if((mode==="measure"||mode==="graph")&&args.length===2){
  const a=await load(args[0],args[1],p);
  out=mode==="graph"?lib.graph(a.snapshot,ROOTS,a.owners):{...lib.report(a.snapshot,ROOTS,a.owners),export_sha256:a.export_sha256,ownership_sha256:a.ownership_sha256};
 }else if(mode==="compare"&&args.length===4){
  const a=await load(args[0],args[1],p),b=await load(args[2],args[3],p);
  out={...lib.compare(a.snapshot,b.snapshot,ROOTS,a.owners,b.owners),inputs:{before:{export_sha256:a.export_sha256,ownership_sha256:a.ownership_sha256},after:{export_sha256:b.export_sha256,ownership_sha256:b.ownership_sha256}}};
  if(!out.structural_guard_passed)process.exitCode=1;
 }else throw Error("usage: node export_metrics_cli.mjs measure|graph EXPORT OWNER|- ; compare OLD_EXPORT OLD_OWNER NEW_EXPORT NEW_OWNER");
 console.log(JSON.stringify(out,null,2));
}catch(e){console.error(e.message);process.exitCode=2}
