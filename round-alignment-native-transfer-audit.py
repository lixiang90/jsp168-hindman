"""Full author-side audit of genuine finite-density/native rough proportions.
Records progress only; no independent replay or final Hindman theorem claimed.
"""
from pathlib import Path
import hashlib, importlib.util, json, re, subprocess, sys, time, tomllib

PREFIX='round-alignment-native-transfer'
OLD='round-alignment-joint-native'
BASELINE='round-alignment-native-transfer-baseline.json'
MODULES=['Hindman168/RoughCoordinateSamplingReindex.lean', 'Hindman168/NativeCoordinateSourceReindex.lean', 'Hindman168/NativeRealResidualEventReindex.lean', 'Hindman168/ComplexMeanObservableApproximation.lean', 'Hindman168/AlignmentNativeCoordinateWindowCap.lean', 'Hindman168/NativeRealResidualObservableApproximation.lean', 'Hindman168/AlignmentNativeCompactTestWindow.lean', 'Hindman168/AlignmentJointResidualTestFamily.lean', 'Hindman168/AlignmentJointOriginalTestWindow.lean', 'Hindman168/AlignmentActualRetainedScaleRange.lean']
EXTERNAL=[]
COMPONENTS=['Genuine spatial coordinate equivalences preserve the entire original box/residue sample sets, counts, uniform laws and complex means, including algebraic empty-set semantics. The removed NONE parameter is retained. Vector substitution preserves degree and the all-real native log, and commutes with the original spatial residual source. Original non-strict real ceil-box bad events transfer exactly to Fin coordinates.', 'Uniform complex observable approximation controls each normalized mean by epsilon and the q/q*t discrepancy by two epsilon. Original non-strict eta events enter genuine eta/2 bounded Lipschitz events through one compact-family approximation chosen before every source, box, compatible residue and removed factor. No nonempty probability assumption or gcd(q,t) is inserted.', 'The proved all-anchor native dyadic-window cap now handles any genuine finite spatial index and compact original observation family. The actual finite JOINT product test family is compact; the actual one-factor JOINT source supplies its degree and ALL-REAL normalized log packet outright. One eventual cutoff precedes every original supported typical anchor and source data. Retained residue/normalization and scale-range are still explicit ordinary arithmetic inputs, not assumed analytic caps.', 'Actual retained factor products from original dyadic residue windows are bounded in both directions by 2^T.card times the original anchor product. This derives a fixed normalized scale range with reference divisor 2^T.card and ratio (2^T.card)^2. The actual exposed cube scale is preserved by the original short-exposure key, and the range is proved on the actual original supported posterior tuples.']
REMAINING='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Exact spatial coordinate/log/source/box/mean/event transfer, two-mean approximation margin, actual joint-source original-test all-anchor window caps and genuine actual retained-product scale ranges are proved. Remaining: assemble actual fixed retained residue and actual supported rest-factor geometry into the cap, prove actual sampled original product discrepancies enter these events, apply posterior Fubini to the actual removal events; face/cube/Alignment and countable diagonal synthesis; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse with sufficient native step for the actual finite degree list; final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
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
 before=tomllib.loads(read('round-alignment-native-transfer-lakefile-before.toml'))
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
