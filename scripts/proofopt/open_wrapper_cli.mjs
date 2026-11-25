import {readFileSync,writeFileSync} from 'node:fs';
import {makePass} from './open_wrapper_pass.mjs';
const [input,output,report]=process.argv.slice(2);
if(!input||!output||!report||new Set([input,output,report]).size!==3)throw Error('usage: node open_wrapper_cli.mjs INPUT OUTPUT REPORT (distinct files)');
const r=makePass().rewrite(readFileSync(input,'utf8'));
writeFileSync(output,r.source,{flag:'wx'});
writeFileSync(report,JSON.stringify(r.report,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({replaced:r.report.replaced_calls,callers:r.report.rewritten_callers,kernel_verified:false}));
