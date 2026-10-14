from pathlib import Path
import hashlib, json, shutil, subprocess

base=Path.cwd()
source=Path('E:/codex-build/math')
candidate=base/'dependencies/openai-dense-progressions'
data=json.loads((base/'openai-dense-progression-dependency-investigation.json').read_text(encoding='utf-8'))
assert not data['forbidden_modules'] and not data['missing_modules']
assert all(m=='Mathlib' or m.startswith('Mathlib.') for m in data['external_imports'])
assert subprocess.run(['git','-C',str(source),'rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip()==data['source_commit']
assert not subprocess.run(['git','-C',str(source),'status','--short','--','lean/OAI'],capture_output=True,text=True,check=True).stdout.strip()
candidate.mkdir(parents=True,exist_ok=True)
manifest=[]
for name,entry in data['files'].items():
 path=Path(entry['path'])
 raw=path.read_bytes()
 assert hashlib.sha256(raw).hexdigest()==entry['sha256'],name
 relative=Path(name.replace('.','/')+'.lean')
 target=candidate/relative
 target.parent.mkdir(parents=True,exist_ok=True)
 target.write_bytes(raw)
 manifest.append(dict(module=name,path=relative.as_posix(),original_sha256=entry['sha256']))
for name in ['LICENSE','NOTICE']:
 path=source/name
 if path.exists(): shutil.copyfile(path,candidate/name)
original_manifest=json.loads((base/'lake-manifest.json').read_text(encoding='utf-8'))
original_manifest['packagesDir']=(base/'.lake/packages').as_posix()
original_manifest['name']='openai_dense_progressions_candidate'
(candidate/'lake-manifest.json').write_text(json.dumps(original_manifest,indent=2),encoding='utf-8')
(candidate/'lean-toolchain').write_bytes((base/'lean-toolchain').read_bytes())
(candidate/'lakefile.toml').write_text('''name = "openai_dense_progressions_candidate"
version = "0.1.0"

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "905b95818eb32af7874a58b427f50c1711a5e96c"

[[lean_lib]]
name = "OAI"
''',encoding='utf-8')
(candidate/'SOURCE-MANIFEST.json').write_text(json.dumps(dict(
 classification='ISOLATED UNVERIFIED CANDIDATE; not a registered project dependency',
 source_commit=data['source_commit'],source_url='https://github.com/openai/math/tree/'+data['source_commit']+'/lean',
 original_toolchain=data['toolchain'],candidate_toolchain=(base/'lean-toolchain').read_text(encoding='utf-8').strip(),
 target='OAI.Combinatorics.Progressions.Results.Conclusions',
 theorem='OAI.Erdos3.manuscriptQuantitativeDensityTheorem',
 files=manifest,local_originals_hash_verified=True,source_worktree_clean=True,
 comparator_module_copied=False,proof_sources_unmodified=True),indent=2),encoding='utf-8')
(candidate/'README.txt').write_text('''OpenAI dense-progression candidate, isolated verification only.
Source: https://github.com/openai/math/tree/'''+data['source_commit']+'''/lean
Copyright/authorship: original OpenAI contributors; Apache-2.0 (LICENSE copied).
Original source toolchain is Lean 4.34.1. This candidate tests unchanged source
against this project's pinned Lean 4.32.2 / mathlib, without changing main pins.
No comparator challenge or sorry module is copied. No dependency is imported
into Hindman168. Source manifests/hashes and later compatibility edits must be
retained and attributed. A source scan or partial build is NOT proof verification.
Require terminal full selected build, original semantic review and transitive
standard-only axiom audit before treating the result as a usable dependency.
''',encoding='utf-8')
print(json.dumps(dict(path=candidate.as_posix(),modules=len(manifest),source_bytes=data['total_source_bytes'],
                     project_proof_sources_changed=False,candidate_verified=False)))
