from pathlib import Path
import hashlib,json

base=Path.cwd()
root=base/'dependencies/openai-dense-progressions'
original=base/'openai-mathlib-exterior-power-original.lean'
raw=original.read_bytes()
assert b'Authors: Justus Springer' in raw
assert b'public import Mathlib.LinearAlgebra.ExteriorPower.Basis' in raw
name='OAI.Compatibility.MathlibExteriorPower'
path=Path(name.replace('.','/')+'.lean')
target=root/path
target.parent.mkdir(parents=True,exist_ok=True)
if not target.exists():
 target.write_bytes(raw)
manifest=root/'SOURCE-MANIFEST.json'
data=json.loads(manifest.read_text(encoding='utf-8'))
entry=dict(module=name,path=path.as_posix(),original_sha256=hashlib.sha256(raw).hexdigest(),
 immutable_original_path=original.as_posix(),
 upstream_repository='https://github.com/leanprover-community/mathlib4',
 upstream_commit='d13f23b723b8a846827a245b89c10fc7d3f11612',
 upstream_path='Mathlib/Analysis/InnerProductSpace/ExteriorPower.lean',
 authors=['Justus Springer'],license='Apache-2.0',
 classification='ATTRIBUTED COMPATIBILITY CANDIDATE; not yet a verified proof input')
existing=[i for i in data['files'] if i['module']==name]
if existing:
 assert existing==[entry]
else:
 data['files'].append(entry)
 manifest.write_text(json.dumps(data,indent=2),encoding='utf-8')
(root/'MATHLIB-COMPATIBILITY-PROVENANCE.json').write_text(json.dumps([entry],indent=2),encoding='utf-8')
print(json.dumps(dict(module=name,original_sha256=entry['original_sha256'],verified=False)))
