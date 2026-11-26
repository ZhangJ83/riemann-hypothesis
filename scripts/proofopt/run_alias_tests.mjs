import fs from "node:fs";
import {run} from "./test_alias_optimizer.mjs";
if(!process.argv[2])throw Error("usage: node run_alias_tests.mjs Nat.add_succ.ndjson");
console.log(JSON.stringify(run(fs.readFileSync(process.argv[2],"utf8")),null,2));
