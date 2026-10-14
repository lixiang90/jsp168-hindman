from pathlib import Path
import hashlib, importlib.util, json, re, subprocess

root=Path('E:/codex-build/math/lean')
spec=importlib.util.spec_from_file_location('helpers','round-native-rational-subgroup-span-audit.py')
helpers=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
seen={}
external=set()
missing=[]
pending=['OAI.Combinatorics.Progressions.Results.Conclusions']
while pending:
 module=pending.pop()
 if module in seen: continue
 path=root/Path(module.replace('.','/')+'.lean')
 if not path.exists():
  missing.append(module)
  continue
 raw=path.read_bytes()
 code=helpers.lean_code(raw.decode('utf-8-sig'))
 imports=re.findall(r'^\s*(?:public\s+)?import\s+([^\r\n]+)',code,re.M)
 names=[name for line in imports for name in line.split()]
 forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code)
 seen[module]=dict(path=path.as_posix(),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),
                   imports=names,forbidden_tokens=forbidden)
 for name in names:
  if name.startswith('OAI.'):
   pending.append(name)
  else:
   external.add(name)
data=dict(classification='UNVERIFIED CANDIDATE, not an imported/proved project dependency',
 source_commit=subprocess.run(['git','-C','E:/codex-build/math','rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip(),
 toolchain=(root/'lean-toolchain').read_text(encoding='utf-8').strip(),
 target='OAI.Erdos3.manuscriptQuantitativeDensityTheorem',
 statement_source='OAI.Combinatorics.Progressions.Model.QuantitativeDensityTheorem',
 selected_module='OAI.Combinatorics.Progressions.Results.Conclusions',
 closure_count=len(seen),total_source_bytes=sum(v['bytes'] for v in seen.values()),
 external_imports=sorted(external),missing_modules=missing,
 forbidden_modules={k:v['forbidden_tokens'] for k,v in seen.items() if v['forbidden_tokens']},
 files=seen,
 comparator_warning='ComparatorChallenges/ErdosReciprocal.lean has sorry and is NOT the solution module; do not import it.',
 scope='Source scan only. No Lean compatibility/kernel/axiom replay or licensing/attribution reuse certification yet. Current project pins unchanged.')
Path('openai-dense-progression-dependency-investigation.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in data.items() if k not in {'files','forbidden_modules'}}))
print(json.dumps(dict(forbidden_module_count=len(data['forbidden_modules']))))
