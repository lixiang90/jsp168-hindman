"""Certify and vendor only the actual fixed-density integer AP closure.
Author-side Lean checking, not independent replay or a Hindman prize proof.
"""
from pathlib import Path
import hashlib, importlib.util, json, re, shutil, subprocess, time

base=Path.cwd()
candidate=base/'dependencies/openai-dense-progressions'
target=base/'dependencies/openai-finite-szemeredi'
spec=importlib.util.spec_from_file_location('audit_helpers','round-native-rational-subgroup-span-audit.py')
helpers=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
digest=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p: json.loads(Path(p).read_text(encoding='utf-8'))
selected=read('openai-finite-szemeredi-selected-closure.json')['modules']
progress=read('openai-finite-szemeredi-progress.json')
assert progress['terminal'] and progress['all_modules_built'] and not progress['failures']
assert progress['completed']==progress['total']==len(selected)==42
records=read('openai-finite-szemeredi-results.json')
manifest=read(candidate/'SOURCE-MANIFEST.json')
entries={i['module']:i for i in manifest['files']}
checked=[]
for name in selected:
    entry=entries[name]
    source=candidate/entry['path']
    result=records[name]
    assert result['terminal'] and result['exit_code']==0
    assert result['source_sha256']==digest(source)
    assert result['log_sha256']==digest(base/result['log'])
    build_log=(base/result['log']).read_text(encoding='utf-8')
    # Retain and explicitly classify the original tactic-style linter output.
    # It neither replaces kernel checking nor justifies ignoring other warnings.
    remainder=re.sub(r"[^\n]+\.lean:\d+:\d+: warning: Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice\s*Note: This linter can be disabled with `set_option linter\.unnecessarySeqFocus false`",'',build_log)
    assert not remainder.strip(),(name,build_log)
    assert result['command']==['lake','env','lean','-DautoImplicit=false',entry['path'],'-o',
        '.lake/build/lib/lean/'+entry['path'].replace('.lean','.olean')]
    assert all(digest(candidate/entries[d]['path'])==h for d,h in result['dependency_source_hashes'].items())
    code=helpers.lean_code(source.read_text(encoding='utf-8'))
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by|unsafe|axiom|run_cmd|elab)\b',code),name
    assert not re.search(r'debug\.skipKernelTC|skipKernel|extern|setOptions',code),name
    checked.append(dict(entry,verified_sha256=digest(source),build_record=result))

cmd=['lake','env','lean','-DautoImplicit=false','FiniteSzemerediAudit.lean']
started=time.monotonic()
log=base/'openai-finite-szemeredi-axioms.txt'
with log.open('wb') as stream:
    result=subprocess.run(cmd,cwd=candidate,stdout=stream,stderr=subprocess.STDOUT)
assert result.returncode==0,log.read_text(encoding='utf-8')[:1500]
text=log.read_text(encoding='utf-8')
assert not re.search(r'warning:|error:',text)
reports=helpers.reports(str(log))
expected={
    'OAI.Erdos3.FixedDensity.szemeredi',
    'OAI.Erdos3.FixedDensity.cyclicAPVal_isIntegerAP',
    'OAI.Erdos3.fixed_density_hasAP',
    'JSP168DependencyAudit.actual_finite_dense_progression',
}
assert set(reports)==expected and all(a<=helpers.ALLOWED for a in reports.values())
assert subprocess.check_output(['lake','env','lean','--version'],cwd=candidate,text=True).startswith('Lean (version 4.32.2,')
assert subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()=='905b95818eb32af7874a58b427f50c1711a5e96c'

target.mkdir(parents=True,exist_ok=True)
for entry in checked:
    output=target/entry['path']
    output.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(candidate/entry['path'],output)
for filename in ['LICENSE','API-COMPATIBILITY-EDITS.json','FINITE-INTEGER-AP-PROVENANCE.json']:
    shutil.copyfile(candidate/filename,target/filename)
shutil.copyfile(candidate/'FiniteSzemerediAudit.lean',target/'FiniteSzemerediAudit.lean')
report=dict(classification='AUTHOR-CHECKED MINIMAL FINITE SZEMEREDI CLOSURE',
    source_repository='https://github.com/openai/math',source_commit=manifest['source_commit'],
    original_toolchain=manifest['original_toolchain'],verified_toolchain='leanprover/lean4:v4.32.2',
    mathlib_commit='905b95818eb32af7874a58b427f50c1711a5e96c',
    original_authorship='OpenAI math contributors; Apache-2.0',
    scope='Fixed-density arbitrary-length finite integer AP only; not the quantitative reciprocal-sum theorem.',
    files=checked,axiom_audit=dict(command=cmd,terminal=True,exit_code=result.returncode,
        elapsed_seconds=time.monotonic()-started,log=log.name,log_sha256=digest(log),
        reports={n:sorted(a) for n,a in reports.items()},audit_source_sha256=digest(candidate/'FiniteSzemerediAudit.lean')),
    permitted_build_warnings='Only the recorded unnecessarySeqFocus tactic-style linter; no options suppressed.',
    semantic_review=[
        'HasAP expands to an actual natural start, strictly positive natural difference and all indices below arbitrary k.',
        'Density theorem quantifies over every positive real density, all sufficiently large N and every subset of range N.',
        'Uniform cyclic count uses all positive cyclic moduli; diagonal mass is removed before extracting a nonzero difference.',
        'The four-times-longer modulus and short-interval reconstruction produce an integer AP; negative integer differences are reversed.',
        'Independent author bridge explicitly gives positive b<K and actual Finset membership, including H=0 and H=1.',
        'API edits close reflexive conversion goals and replace names/imports without changing original statements or assumptions.',
    ],independent_kernel_replay=False,external_peer_review=False,full_hindman_target_proved=False)
(target/'SOURCE-MANIFEST.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
(base/'openai-finite-szemeredi-certification.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
(target/'README.txt').write_text(
    'Minimal attributed finite Szemeredi dependency for JSP-000168.\n'
    'Original source: OpenAI math, commit '+manifest['source_commit']+'.\n'
    'Copyright: original OpenAI contributors; Apache-2.0.\n'
    '42 selected modules checked under Lean 4.32.2 and pinned mathlib.\n'
    'SOURCE-MANIFEST.json records exact sources, hashes, build logs and transitive target axioms.\n'
    'API-COMPATIBILITY-EDITS.json records compatibility changes; original mathematical assumptions retained.\n'
    'The independent author bridge is in FiniteSzemerediAudit.lean.\n'
    'This verifies finite density/AP input only. It is not a proof of Hindman FS/FP,\n'
    'independent kernel replay, the full reciprocal-sum result, or an award submission.\n',encoding='utf-8')
print(json.dumps(dict(modules=len(selected),target_axiom_audits=len(reports),standard_axioms_only=True,
    full_hindman_target_proved=False,output=str(target))))
