from pathlib import Path
import concurrent.futures,hashlib,json,os,re,subprocess,time,functools

base=Path.cwd()
root=base/'dependencies/openai-dense-progressions'
original=json.loads((root/'SOURCE-MANIFEST.json').read_text(encoding='utf-8'))
records_path=base/'openai-finite-szemeredi-results.json'
records=json.loads((records_path if records_path.exists() else base/'openai-dense-progression-bounded-results.json').read_text(encoding='utf-8'))
paths={item['module']:root/item['path'] for item in original['files']}
deps={}
hashes={}
for name,path in paths.items():
 raw=path.read_bytes()
 hashes[name]=hashlib.sha256(raw).hexdigest()
 deps[name]={m for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\r\n]+)',raw.decode('utf-8-sig'),re.M)
             for m in line.split() if m.startswith('OAI.')}
 assert deps[name]<=paths.keys(),(name,deps[name]-paths.keys())
selected_targets={
 'OAI.Combinatorics.Progressions.FixedDensity.Conclusions',
 'OAI.Combinatorics.Progressions.FixedDensity.CountExtraction',
 'OAI.Compatibility.FiniteIntegerAP',
}
selected=set()
def select(name):
 if name in selected: return
 selected.add(name)
 for d in deps[name]: select(d)
for name in selected_targets: select(name)
paths={name:path for name,path in paths.items() if name in selected}
deps={name:ds for name,ds in deps.items() if name in selected}
hashes={name:h for name,h in hashes.items() if name in selected}
(base/'openai-finite-szemeredi-selected-closure.json').write_text(json.dumps(dict(
 target='OAI.Erdos3.fixed_density_hasAP',modules=sorted(selected),
 total=len(selected),provenance_manifest='dependencies/openai-dense-progressions/SOURCE-MANIFEST.json',
 classification='SOURCE CLOSURE ONLY; not yet a certified proof dependency'),indent=2),encoding='utf-8')
@functools.cache
def closure_fingerprint(name):
 return hashlib.sha256(json.dumps([hashes[name],[(d,closure_fingerprint(d)) for d in sorted(deps[name])]],
                                 separators=(',',':')).encode()).hexdigest()
fingerprints={name:closure_fingerprint(name) for name in paths}
remaining=set(paths)
done=set()
failures=[]
start=time.monotonic()
env=dict(os.environ,LEAN_NUM_THREADS='2')
logs=base/'openai-finite-szemeredi-logs'
logs.mkdir(exist_ok=True)
def run(name):
 path=paths[name]
 log=logs/(name+'.txt')
 relative=path.relative_to(root)
 output=Path('.lake/build/lib/lean')/relative.with_suffix('.olean')
 (root/output).parent.mkdir(parents=True,exist_ok=True)
 cmd=['lake','env','lean','-DautoImplicit=false',relative.as_posix(),'-o',output.as_posix()]
 t=time.monotonic()
 with log.open('wb') as stream:
  result=subprocess.run(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
 data=log.read_bytes()
 return name,dict(command=cmd,terminal=True,exit_code=result.returncode,
                  elapsed_seconds=time.monotonic()-t,source_sha256=hashes[name],
                  transitive_source_fingerprint=fingerprints[name],
                  dependency_source_hashes={d:hashes[d] for d in sorted(deps[name])},
                  log=log.relative_to(base).as_posix(),log_sha256=hashlib.sha256(data).hexdigest(),
                  warnings=bool(re.search(rb'(?:warning:|error:)',data)))
def save():
 records_path.write_text(json.dumps(records,indent=2),encoding='utf-8')
 (base/'openai-finite-szemeredi-progress.json').write_text(json.dumps(dict(
  classification='CANDIDATE ONLY; not a certified project dependency',terminal=False,
  completed=len(done),total=len(paths),failures=failures,elapsed_seconds=time.monotonic()-start,
  max_parallel_lake_processes=2,toolchain='4.32.2'),indent=2),encoding='utf-8')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 active={}
 while remaining or active:
  ready=sorted((name for name in remaining if deps[name]<=done),
               key=lambda name:(not name.startswith('OAI.Compatibility.'),name))
  for name in ready:
   if len(active)>=2 or len(failures)>=4: break
   prior=records.get(name)
   olean=root/'.lake/build/lib/lean'/Path(name.replace('.','/')+'.olean')
   if (prior and prior['terminal'] and prior['exit_code']==0 and prior['command'][:3]==['lake','env','lean'] and prior['source_sha256']==hashes[name]
       and prior.get('transitive_source_fingerprint')==fingerprints[name]
       and prior['dependency_source_hashes']=={d:hashes[d] for d in sorted(deps[name])}
       and olean.exists() and olean.stat().st_mtime_ns>=paths[name].stat().st_mtime_ns):
    done.add(name);remaining.remove(name)
    continue
   active[pool.submit(run,name)]=name
   remaining.remove(name)
  if not active:
   if failures: break
   if ready: continue
   raise RuntimeError('Missing dependency or import cycle '+repr(sorted(remaining)[:5]))
  completed,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in completed:
   active.pop(future)
   name,result=future.result()
   records[name]=result
   if result['exit_code']==0:
    done.add(name)
    if len(done)%25==0: print('Verified '+str(len(done))+'/'+str(len(paths)),flush=True)
   else:
    failures.append(name)
    print('FAILED '+name+'; see '+result['log'],flush=True)
  save()
  if len(failures)>=4 and not active: break
save()
summary=dict(classification='CANDIDATE ONLY; not a certified project dependency',terminal=True,
 completed=len(done),total=len(paths),failures=failures,elapsed_seconds=time.monotonic()-start,
 max_parallel_lake_processes=2,all_modules_built=len(done)==len(paths),
 selected_target_built='OAI.Compatibility.FiniteIntegerAP' in done,
  uniform_cyclic_target_built='OAI.Combinatorics.Progressions.FixedDensity.Conclusions' in done,
  count_extraction_built='OAI.Combinatorics.Progressions.FixedDensity.CountExtraction' in done,
 standard_axiom_audit_done=False,main_project_dependency=False)
(base/'openai-finite-szemeredi-progress.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
print(json.dumps(summary),flush=True)
raise SystemExit(1 if failures else 0)
