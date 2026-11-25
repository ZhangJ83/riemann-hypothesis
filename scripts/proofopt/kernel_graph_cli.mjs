import {readFileSync} from "node:fs";
import {buildGraph,reach,summarize,optimize,readSnapshot,testSuite} from "./kernel_graph.mjs";
const [mode,file,candidates,budget,limit]=process.argv.slice(2);
if(!file) throw new Error("usage: node kernel_graph_cli.mjs test fixture.json | inspect graph.jsonl | optimize graph.jsonl candidates.json budget [maxStates]");
const data=readFileSync(file,"utf8");
if(mode==="test") console.log(JSON.stringify(testSuite(JSON.parse(data)),null,2));
else {
 const g=buildGraph(readSnapshot(data));
 if(mode==="inspect") console.log(JSON.stringify({measurement:g.measurement,union:summarize(g,reach(g)),per_root:[...g.roots].map(root=>({root,...summarize(g,reach(g,[root]))}))},null,2));
 else if(mode==="optimize") console.log(JSON.stringify(optimize(g,JSON.parse(readFileSync(candidates,"utf8")),Number(budget),limit===undefined?100000:Number(limit)),null,2));
 else throw new Error("unknown mode");
}
