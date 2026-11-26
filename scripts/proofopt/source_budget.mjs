import {execFileSync} from "node:child_process";
import {writeFileSync} from "node:fs";
import {pathToFileURL} from "node:url";

// Conservative whole-project source accounting. Count comments too, and prevent
// packing a long line into a single line from meeting the budget.
export function countSource(source) {
  const lines=source.replaceAll("\r\n","\n").split("\n");
  if(lines.at(-1)==="") lines.pop();
  let nonblank=0, wrapped=0;
  for(const line of lines) {
    if(!line.trim()) continue;
    nonblank++;
    let width=0;
    for(const ch of line) width+=ch==="\t" ? 4-(width%4) : 1;
    wrapped+=Math.max(1,Math.ceil(width/100));
  }
  return {physical:lines.length,nonblank,wrapped,bytes:Buffer.byteLength(source)};
}
export function summarize(entries) {
  const total={files:0,physical:0,nonblank:0,wrapped:0,bytes:0};
  const seen=new Set();
  for(const [path,source] of entries) {
    if(!/^src\/.+\.lean$/.test(path) || path.split("/").includes("..") || seen.has(path)) throw Error("invalid or duplicate project source");
    seen.add(path); total.files++;
    for(const [key,val] of Object.entries(countSource(source))) total[key]+=val;
  }
  if(!total.files) throw Error("empty source scope");
  return {...total,target:2000,withinBudget:total.nonblank<=2000 && total.wrapped<=2000};
}
const git=args=>execFileSync("git",args,{encoding:"utf8",maxBuffer:64*1024*1024});
function measure(ref) {
  const sha=git(["rev-parse","--verify",ref+"^{commit}"]).trim();
  const paths=git(["ls-tree","-rz","--name-only",sha,"src"]).split("\0").filter(p=>p.endsWith(".lean"));
  return {sha,...summarize(paths.map(p=>[p,git(["show",sha+":"+p])]))};
}
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) {
  const [base,head,out]=process.argv.slice(2);
  if(!/^[0-9a-f]{40}$/.test(base??"") || !head || !out) throw Error("usage: node source_budget.mjs BASE_SHA HEAD OUTPUT");
  writeFileSync(out,JSON.stringify({schema:1,metric:"all tracked src/**/*.lean; nonblank incl comments; fixed 100-codepoint wrapping; not a proof check",base:measure(base),candidate:measure(head)},null,2)+"\n");
}
