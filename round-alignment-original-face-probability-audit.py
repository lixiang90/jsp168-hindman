"""Full author-side audit of genuine finite-density/native rough proportions.
Records progress only; no independent replay or final Hindman theorem claimed.
"""
from pathlib import Path
import hashlib, importlib.util, json, re, subprocess, sys, time, tomllib

PREFIX='round-alignment-original-face-probability'
OLD='round-alignment-integer-face-state'
BASELINE='round-alignment-original-face-probability-baseline.json'
MODULES=['Hindman168/AlignmentOriginalProductFaceFailure.lean', 'Hindman168/AlignmentOriginalProductFacePosterior.lean', 'Hindman168/AlignmentOriginalProductFaceFiniteFamily.lean', 'Hindman168/AlignmentOriginalProductAllFacesPosterior.lean', 'Hindman168/FiniteTypicalExposureEventBound.lean', 'Hindman168/AlignmentOriginalProductAllFacesGlobal.lean', 'Hindman168/AlignmentOriginalProductFacePositiveSelection.lean']
EXTERNAL=[]
COMPONENTS=['The LITERAL original marginal product cube face failure compares original nilsequence cube means at unchanged original slots and their genuine own-pair face-shifted slots. The event retains ALL original permitted boxes/residues and original numerical bounded/Lipschitz observers after the sampled tuple. Its ACTUAL posterior probability vanishes: BOTH original-to-terminal removal errors and the genuine terminal face discrepancy are combined with epsilon/3 and delta/2 budgets; actual support/key identities identify the SAME endpoint origin and terminal denominator choices. Conditional independence is never assumed.', 'ONE actual posterior cutoff covers every fixed finite family of original own pairs, face coordinates, slots, vertex profiles and observer bounds. The COMPLETE fixed finite list of ALL original own pairs, ALL coordinates and ALL zero/one vertex profiles is instantiated with exact Fin 2 representation. The failing face/vertex profile can be chosen AFTER the sampled tuple. No unbounded arbitrary-integer-weight union is asserted, and empty face lists stay empty.', 'Exact original exposure disintegration integrates good-key conditional event caps to the original raw law, charging bad keys their ACTUAL original mass. The original marginal product all-face failure now vanishes uniformly BEFORE every original source formula selected by the actual exposed key. Bad-key mass is PROVED to vanish; original formulae can vary with width and exposed key, but never with unexposed factors in this result.', 'For arbitrary width-varying original exposed-key source selections the actual original all-face failure probability tends to zero. ANY additional actual conditioning of probability bounded below preserves the zero limit and yields supported ORIGINAL samples in that prescribed set satisfying all original own faces and zero/one vertex profiles at fixed numerical tolerances. Full continuous cube test classes, countable diagonal simultaneity and cube limits/Alignment remain work; product-observation results are not relabeled as those stronger conclusions.']
REMAINING='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original marginal PRODUCT-observation cube face discrepancy now vanishes under ACTUAL posterior and original global law, uniformly in original boxes/residues/tests and ALL own pairs/coordinates/zero-one vertex profiles, with genuine exposed-key-selected width-varying source formulae. Positive-mass extra conditioning preserves failure vanishing and admits supported original samples. Remaining: promote product observations through the original complete marginal continuous cube test class (finite product-span approximation as needed), obtain one countable numerical-condition/target/dimension diagonal sequence compatible with original master/data selections, and prove cube limits/local cube coset face invariance/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse with sufficient native step for actual finite degree list; final positive distinct rapidly separated monochromatic FS/FP. No other-component invariance, unexposed-factor-dependent formula uniformity or explicit delta-power law asserted. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
spec=importlib.util.spec_from_file_location('helpers','round-native-rational-subgroup-span-audit.py')
helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
read,obj,digest,write=helpers.read,helpers.obj,helpers.digest,helpers.write_obj

def decls():
 return {p:re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([A-Za-z][A-Za-z0-9_.]*)',helpers.lean_code(read(p)),re.M) for p in MODULES}

def names():
 return ['Hindman168.'+n for ds in decls().values() for _,n in ds]+EXTERNAL

def diagnostics(log,dependency_lints=False):
 text=read(log)
 assert 'error:' not in text,log
 warnings=re.findall(r'^warning: ([^\n]+)',text,re.M)
 if not dependency_lints: assert not warnings,log
 else:
  for warning in warnings:
   assert re.fullmatch(r'dependencies/openai-finite-szemeredi/OAI/[\w/]+\.lean:\d+:\d+: Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice',warning),warning

def run(command,log,dependency_lints=False):
 start=time.monotonic()
 with open(log,'wb') as stream:
  r=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
 result=dict(command=command,terminal=True,exit_code=r.returncode,elapsed_seconds=time.monotonic()-start,
             log=log,log_sha256=digest(log))
 assert r.returncode==0,(command,read(log)[-3000:])
 diagnostics(log,dependency_lints)
 return result

def config_check(baseline):
 before=tomllib.loads(read('round-alignment-original-face-probability-lakefile-before.toml'))
 after=tomllib.loads(read('lakefile.toml'))
 expected=dict(before)
 expected['lean_lib']=before['lean_lib']
 assert after==expected
 assert before['require']==after['require'] and before['leanOptions']==after['leanOptions']
 assert helpers.run(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'])==baseline['mathlib_commit']
 assert helpers.run(['git','-C','../reference-pntplus','rev-parse','HEAD'])==baseline['pntplus_commit']
 assert 'version 4.32.2,' in helpers.run(['lake','env','lean','--version'])

def dependency_check():
 certificate=obj('openai-finite-szemeredi-certification.json')
 root=Path('dependencies/openai-finite-szemeredi')
 assert obj(root/'SOURCE-MANIFEST.json')==certificate
 assert len(certificate['files'])==42
 assert certificate['axiom_audit']['exit_code']==0 and certificate['axiom_audit']['terminal']
 assert certificate['axiom_audit']['log_sha256']==digest(certificate['axiom_audit']['log'])
 files=[]
 for item in certificate['files']:
  path=root/item['path']
  assert digest(path)==item['verified_sha256']
  code=helpers.lean_code(read(path))
  assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by|unsafe|axiom|run_cmd|elab)\b',code),path
  assert not re.search(r'skipKernelTC|skipKernel|setOptions|extern',code),path
  files.append(dict(path=path.as_posix(),sha256=digest(path)))
 for name in ['LICENSE','SOURCE-MANIFEST.json','FINITE-INTEGER-AP-PROVENANCE.json','API-COMPATIBILITY-EDITS.json','README.txt','FiniteSzemerediAudit.lean']:
  path=root/name
  files.append(dict(path=path.as_posix(),sha256=digest(path)))
 return files

def prepare():
 baseline=obj(BASELINE)
 assert baseline==obj('verification-manifest.json')
 assert all(digest(f['path'])==f['sha256'] for f in baseline['files'] if f['path'] not in {'Hindman168.lean','Verification.lean'})
 config_check(baseline);dependency_check()
 results=[]
 for p in MODULES:
  log=PREFIX+'-'+Path(p).stem+'-focused.txt'
  result=run(['lake','env','lean','-DautoImplicit=false',p],log)
  assert not Path(log).read_bytes().strip()
  results.append(dict(result,module=p,source_sha256=digest(p)))
  print('Explicitly checked '+p,flush=True)
 write(PREFIX+'-focused-results.json',results)
 root,registry=read('Hindman168.lean'),read('Verification.lean')
 for p in MODULES:
  line='import '+p[:-5].replace('/','.')
  if line not in root.splitlines(): root+='\n'+line+'\n'
 for name in names():
  line='#print axioms '+name
  if line not in registry.splitlines(): registry+='\n'+line+'\n'
 Path('Hindman168.lean').write_text(root,encoding='utf-8')
 Path('Verification.lean').write_text(registry,encoding='utf-8')
 write(PREFIX+'-registration.json',dict(modules=MODULES,names=names(),declarations=decls()))

def check():
 baseline=obj(BASELINE)
 changed={f['path'] for f in baseline['files'] if digest(f['path'])!=f['sha256']}
 assert changed=={'Hindman168.lean','Verification.lean'},changed
 config_check(baseline)
 dependency_files=dependency_check()
 own=sorted(Path('Hindman168').glob('*.lean'));pnt=sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
 assert {p.as_posix() for p in own}=={f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')}|set(MODULES)
 imports=re.findall(r'^import (Hindman168\.\S+)',read('Hindman168.lean'),re.M)
 assert len(imports)==len(set(imports))==len(own)
 assert set(imports)=={p.with_suffix('').as_posix().replace('/','.') for p in own}
 for p in own+pnt+[Path('Hindman168.lean'),Path('Verification.lean')]:
  code=helpers.lean_code(read(p))
  assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b',code),p
  assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b',code,re.M),p
 for p in MODULES:
  assert not re.search(r'\b(?:set_option|setOptions|instance|structure)\b',helpers.lean_code(read(p))),p
  assert (Path('.lake/build/lib/lean')/Path(p).with_suffix('.olean')).stat().st_mtime_ns>=Path(p).stat().st_mtime_ns
 results=obj(PREFIX+'-focused-results.json')
 assert [r['module'] for r in results]==MODULES
 for r in results:
  assert r['terminal'] and r['exit_code']==0 and r['source_sha256']==digest(r['module'])
  assert r['log_sha256']==digest(r['log']) and not read(r['log']).strip()
 for kind in ['build','axioms']:
  r=obj(PREFIX+'-'+kind+'-result.json')
  assert r['terminal'] and r['exit_code']==0 and r['log_sha256']==digest(r['log'])
  diagnostics(r['log'],kind=='build')
 previous,actual=helpers.reports(OLD+'-axioms.txt'),helpers.reports(PREFIX+'-axioms.txt')
 registered=re.findall(r'^#print axioms (\S+)',read('Verification.lean'),re.M)
 assert len(registered)==len(set(registered))==len(actual)
 assert set(registered)==set(actual) and set(actual)-set(previous)==set(names())
 assert all(actual[n]==a for n,a in previous.items())
 assert all(a<=helpers.ALLOWED for a in actual.values())
 fixed=obj(OLD+'-preprint-local-check.json')
 for section in fixed['sections']:
  raw=(Path('E:/codex-build/math')/section['path']).read_bytes().replace(b'\r\n',b'\n')
  pinned=subprocess.check_output(['git','-C','E:/codex-build/math','show',fixed['fixed_openai_math_commit']+':'+section['path']]).replace(b'\r\n',b'\n')
  assert raw==pinned and hashlib.sha256(raw).hexdigest()==section['normalized_sha256']
 files=[dict(path=f['path'],sha256=digest(f['path'])) for f in baseline['files']]
 files += [dict(path=p,sha256=digest(p)) for p in MODULES]
 assert all(any(old['path']==dep['path'] and old['sha256']==dep['sha256'] for old in files) for dep in dependency_files)
 jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',read(PREFIX+'-build.txt'));assert len(jobs)==1
 summary=dict(project_modules=len(own),pntplus_modules=len(pnt),attributed_szemeredi_modules=42,
  build_jobs=int(jobs[0]),selected_axiom_reports=len(actual),new_declarations=sum(map(len,decls().values())),
  new_theorems=sum(k in {'theorem','lemma'} for ds in decls().values() for k,_ in ds),
  new_definitions=sum(k in {'def','abbrev'} for ds in decls().values() for k,_ in ds),
  new_external_targets=len(EXTERNAL),retained_proof_sources_unchanged=True,retained_axiom_sets_unchanged=True,
  standard_axioms_only=True,main_pins_unchanged=True,full_target_proved=False,independent_kernel_replay=False)
 return baseline,files,summary,fixed

def record():
 baseline,files,summary,fixed=check()
 review=dict(date='2026-10-14',classification='PROGRESS',full_target_proved=False,verified=summary,
  new_modules=MODULES,proved_components=COMPONENTS,remaining=REMAINING,
  mathematical_review_file=PREFIX+'-mathematical-review.txt',mathematical_review_sha256=digest(PREFIX+'-mathematical-review.txt'),
  primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
  dependency_certification='openai-finite-szemeredi-certification.json',dependency_certification_sha256=digest('openai-finite-szemeredi-certification.json'))
 manifest=dict(baseline)
 manifest.update(date='2026-10-14',files=files,hindman_module_count=summary['project_modules'],
  attributed_szemeredi_module_count=42,source_scan_module_count=summary['project_modules']+summary['pntplus_modules']+42,
  selected_axiom_report_count=summary['selected_axiom_reports'],build_job_count=summary['build_jobs'],
  build_log=PREFIX+'-build.txt',axiom_log=PREFIX+'-axioms.txt',proved_components=baseline['proved_components']+COMPONENTS,
  last_round=dict(classification='PROGRESS',new_module_count=len(MODULES),new_theorem_count=summary['new_theorems'],
  new_selected_report_count=summary['new_declarations']+len(EXTERNAL),retained_proof_sources_changed=False,
  root_and_registry_changed=True,review_file=PREFIX+'-review.json',remaining=REMAINING))
 write(PREFIX+'-review.json',review);write(PREFIX+'-checks.json',summary);write(PREFIX+'-preprint-local-check.json',fixed)
 write('verification-manifest.json',manifest)
 audit=read('AUDIT.txt');marker='Remaining proof work:'
 assert audit.count(marker)==1 and audit.split(marker)[1].strip()==baseline['last_round']['remaining']
 Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-14 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
 Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n'+Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+Path(PREFIX+'-axioms.txt').read_bytes())
 Path('CURRENT-STATUS.txt').write_text('JSP-000168 / Erdos #172 -- 2026-10-14\n\nVerdict: Partial overall coverage; PROGRESS.\nGoal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction established.\nLatest terminal author audit: '+PREFIX+'\n\n'+'\n\n'.join(COMPONENTS)+'\n\n'+json.dumps(summary,indent=2)+'\n\n'+REMAINING+'\n',encoding='utf-8')
 print(json.dumps(summary),flush=True)

if __name__=='__main__':
 mode=sys.argv[1]
 if mode=='prepare':prepare()
 elif mode=='build':write(PREFIX+'-build-result.json',run(['lake','build'],PREFIX+'-build.txt',True))
 elif mode=='axioms':write(PREFIX+'-axioms-result.json',run(['lake','env','lean','Verification.lean'],PREFIX+'-axioms.txt'))
 elif mode=='record':record()
 elif mode=='recheck':
  _,files,summary,_=check();assert obj('verification-manifest.json')['files']==files;print(json.dumps(summary))
 else:raise ValueError(mode)
