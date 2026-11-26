import fs from "node:fs";
import {lib} from "./export_metrics.mjs";
import {solve} from "./alias_optimizer.mjs";
const [file,ownerFile,budget,limit,...roots]=process.argv.slice(2);
if(!file||!ownerFile||!roots.length)throw Error("usage: node alias_optimizer_cli.mjs EXPORT OWNERS_OR_- BUDGET MAX_STATES ROOT ...");
const s=lib.parse(fs.readFileSync(file,"utf8"));
const own=ownerFile==="-"?null:lib.owners(fs.readFileSync(ownerFile,"utf8").trimEnd().split("\n").map(JSON.parse));
console.log(JSON.stringify(solve(s,roots,{own,budget:Number(budget),maxStates:Number(limit)}),null,2));
