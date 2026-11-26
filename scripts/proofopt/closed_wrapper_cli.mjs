import {readFileSync} from "node:fs";
import {engine} from "./closed_wrapper.mjs";
import {lib} from "./export_metrics.mjs";
const [file,owners,budget,maxStates,...roots]=process.argv.slice(2);
if(!file||!owners||!roots.length)throw Error("usage: node closed_wrapper_cli.mjs export.ndjson ownership.ndjson|- budget maxStates ROOT...");
const s=lib.parse(readFileSync(file,"utf8"),engine.pool());
const own=owners==="-"?null:lib.owners(readFileSync(owners,"utf8").trim().split(/\r?\n/).map(JSON.parse));
console.log(JSON.stringify(engine.solve(s,roots,{own,budget:Number(budget),maxStates:Number(maxStates)}),null,2));
