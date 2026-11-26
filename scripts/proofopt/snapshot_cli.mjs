import {readFileSync,writeFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {makeCore} from "./snapshot.mjs";
const [base, out, ...allowed] = process.argv.slice(2);
if (!/^[0-9a-f]{40}$/.test(base??"") || !out) throw Error("usage: node snapshot_cli.mjs BASE_SHA OUTPUT_DIR");
const core=makeCore();
function read(ref,path){return execFileSync("git",["show",ref+":"+path],{encoding:"utf8"});}
function snap(ref){
 const tree=core.parseTree(execFileSync("git",["ls-tree","-rz",ref],{encoding:"utf8",maxBuffer:64*1024*1024}));
 return core.inventory(tree,JSON.parse(read(ref,"comparator.json")),JSON.parse(read(ref,"lake-manifest.json")),read(ref,"lean-toolchain"));
}
const head=execFileSync("git",["rev-parse","HEAD"],{encoding:"utf8"}).trim();
const reference=snap(base),current=snap(head);
const diff=core.check(reference,current,allowed);
writeFileSync(out+"/snapshot.json",JSON.stringify({base,head,diff,reference,current},null,2)+"\n");
writeFileSync(out+"/modules.txt",current.modules.map(x=>x.module).join("\n")+"\n");
console.log(JSON.stringify(diff));
