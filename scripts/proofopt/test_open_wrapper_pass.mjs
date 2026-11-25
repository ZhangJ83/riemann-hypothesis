// Replays the exact tests used for round 05 on two pinned source files.
import {readFileSync} from 'node:fs';
import {makePass} from './open_wrapper_pass.mjs';
function runTests(makePass,baseline,latest){
 const p=makePass(),a=p.rewrite(baseline),b=p.rewrite(latest);
 const tests=[];const eq=(x,y)=>{if(JSON.stringify(x)!==JSON.stringify(y))throw Error(`expected ${JSON.stringify(y)}; got ${JSON.stringify(x)}`)};
 const test=(name,f)=>{f();tests.push(name)};
 const fail=(f,pattern)=>{let err=null;try{f()}catch(e){err=e}if(!err||!pattern.test(String(err)))throw Error("did not fail as expected: "+String(err))};
 const first="TemperedProductOfSquareIntegrable",second="TopMainZj";
 const ns="UpperTheory.LiteratureTheorems.",prefix="_root_."+ns;
 const counts=r=>[r.report.eligible_wrappers,r.report.rewritten_callers,r.report.replaced_calls,r.report.affected_wrappers,r.report.wrappers_with_only_declaration_text];
 const view=(s,part)=>p.declarations(p.section(s,part).body);
 test("fixed fork baseline integration",()=>eq(counts(a),[25,9,33,22,22]));
 test("current upstream integration",()=>eq(counts(b),[25,9,33,22,22]));
 test("both pinned versions select the same wrapper/caller edges",()=>eq(a.report.edits,b.report.edits));
 test("all 33 call replacements audited",()=>eq(a.report.wrappers.reduce((n,x)=>n+x.replaced,0),33));
 test("each recorded fully-qualified wrapper occurrence falls to its declaration",()=>eq(a.report.wrappers.every(x=>x.before_text_occurrences_in_file-x.remaining_text_occurrences_in_file===x.replaced&&x.remaining_text_occurrences_in_file===1),true));
 test("idempotent baseline",()=>{const r=p.rewrite(a.source);eq(r.source,a.source);eq(r.report.replaced_calls,0)});
 test("idempotent current upstream",()=>eq(p.rewrite(b.source).source,b.source));
 test("headers and wrapper bodies unchanged",()=>{for(const part of [first,second]){const x=view(baseline,part),y=view(a.source,part);eq(x.map(d=>d.header),y.map(d=>d.header));const changed=new Set(a.report.edits.map(e=>e.caller));for(let i=0;i<x.length;i++)if(!changed.has(x[i].name))eq(x[i].value,y[i].value)}});
 test("restoring nine original proof bodies restores the entire source",()=>{let restored=a.source;for(const part of [second,first]){const orig=view(baseline,part),now=p.section(restored,part),ds=p.declarations(now.body);let s=now.body;for(let i=ds.length-1;i>=0;i--)if(ds[i].value!==orig[i].value)s=s.slice(0,ds[i].start+ds[i].header.length)+orig[i].value+s.slice(ds[i].end);restored=restored.slice(0,now.start)+s+restored.slice(now.end)}eq(restored,baseline)});
 test("typed underlying constant replaces OpenImageCondition call",()=>{const d=view(a.source,first).find(x=>x.name===ns+"algebraic_character_wd_of_open");eq(d.value.includes("(show _root_.GlobalTheory.Published.DeRhamPotSemistable from _root_.GlobalTheory.deRham_potentiallySemistable)"),true);eq(d.value.includes(prefix+"de_rham_pot_semistable_of_open O"),false)});
 test("projection-style source terms are not blindly substituted",()=>{eq(a.report.wrappers.some(x=>x.name===ns+"cusp_forms_bounded_gl_of_open"),false);eq(a.source.includes(prefix+"cusp_forms_bounded_gl_of_open O"),true)});
 test("nontrivial dependent wrapper not classified as a simple constant",()=>eq(a.report.wrappers.some(x=>x.name===ns+"gelfand_kazhdan_dual_of_open"),false));
 test("missing clump fails closed",()=>fail(()=>p.rewrite(baseline.replace("."+first+" =====",".NotTheMember =====")),/missing member/));
 test("duplicate clump fails closed",()=>fail(()=>p.rewrite(baseline+"\n-- ===== clump member: Duplicate."+first+" =====\n"),/ambiguous/));
 test("unexpected caller binder fails closed",()=>{const needle="theorem "+ns+"algebraic_character_wd_of_open (O :";fail(()=>p.rewrite(baseline.replace(needle,needle.replace("(O :","(P :"))),/unexpected caller binder/)});
 test("comment in target proof fails closed",()=>{const sec=p.section(baseline,first),d=p.declarations(sec.body).find(x=>x.name===ns+"algebraic_character_wd_of_open");const i=sec.start+d.start+d.header.length;fail(()=>p.rewrite(baseline.slice(0,i)+"  -- changed context\n"+baseline.slice(i)),/unsupported comment/)});
 test("single name with unused parameter required",()=>{const d=view(baseline,first).find(x=>x.name===ns+"de_rham_pot_semistable_of_open");eq(p.candidates([d]).size,1);eq(p.candidates([{...d,value:"  GlobalTheory.deRham_potentiallySemistable O\n"}]).size,0)});
 return {passed:tests.length,tests,baseline:a,upstream:b};
}
const [baseline,upstream]=process.argv.slice(2);
if(!baseline||!upstream) throw Error('usage: node test_open_wrapper_pass.mjs BASELINE_FILE UPSTREAM_FILE');
const r=runTests(makePass,readFileSync(baseline,'utf8'),readFileSync(upstream,'utf8'));
console.log(JSON.stringify({passed:r.passed,tests:r.tests,baseline:r.baseline.report,upstream:r.upstream.report},null,2));
