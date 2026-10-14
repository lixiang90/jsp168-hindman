from pathlib import Path
import hashlib,json

base=Path.cwd()
root=base/'dependencies/openai-dense-progressions'
manifest=root/'SOURCE-MANIFEST.json'
data=json.loads(manifest.read_text(encoding='utf-8'))
original_module='OAI.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter'
entry=next(item for item in data['files'] if item['module']==original_module)
upstream=Path('E:/codex-build/math/lean')/entry['path']
raw=upstream.read_bytes()
assert hashlib.sha256(raw).hexdigest()==entry['original_sha256']
source=raw.decode('utf-8-sig').replace('\r\n','\n')
start=source.index('namespace Erdos3.FixedDensity\n')
end=source.index('\nend Erdos3\n',start)+len('\nend Erdos3\n')
excerpt=source[start:end]
assert 'theorem fixed_density_hasAP' in excerpt
assert 'theorem exists_naturalAP_of_cyclicAPVal_shortInterval' in excerpt
assert 'densityParameter' not in excerpt
imports='''import OAI.Combinatorics.Progressions.Model
import OAI.Combinatorics.Progressions.FixedDensity.Conclusions
import OAI.Combinatorics.Progressions.FixedDensity.CountExtraction
import OAI.Combinatorics.Progressions.FixedDensity.ShortInterval
'''
notice='''
/-! Attributed excerpt from OpenAI math at the pinned commit.
Original: Probability/RelativeSourceDensityParameter.lean.
Only the natural-progression, cyclic interval and fixed-density extraction
declarations are retained. Their mathematical statements and proof bodies
are unchanged here. Apache-2.0; copyright original OpenAI contributors.
See FINITE-INTEGER-AP-PROVENANCE.json for exact whole-source/excerpt hashes.
-/
'''
text=imports+notice+'\nnamespace OAI\nsection\n\n'+excerpt+'\nend\nend OAI\n'
immutable=base/'openai-finite-integer-ap-original.lean'
encoded=text.encode('utf-8')
if immutable.exists():
 assert immutable.read_bytes()==encoded
else:
 immutable.write_bytes(encoded)
name='OAI.Compatibility.FiniteIntegerAP'
path=Path(name.replace('.','/')+'.lean')
target=root/path
target.parent.mkdir(parents=True,exist_ok=True)
if not target.exists(): target.write_bytes(encoded)
new=dict(module=name,path=path.as_posix(),original_sha256=hashlib.sha256(encoded).hexdigest(),
 immutable_original_path=immutable.as_posix(),upstream_commit=data['source_commit'],
 upstream_repository='https://github.com/openai/math',upstream_path=entry['path'],
 upstream_full_sha256=entry['original_sha256'],excerpt_body_sha256=hashlib.sha256(excerpt.encode()).hexdigest(),
 original_start_line=source[:start].count('\n')+1,original_end_line=source[:end].count('\n'),
 classification='ATTRIBUTED SOURCE EXCERPT; not yet a certified dependency',license='Apache-2.0')
old=[item for item in data['files'] if item['module']==name]
if old: assert old==[new]
else:
 data['files'].append(new)
 manifest.write_text(json.dumps(data,indent=2),encoding='utf-8')
(root/'FINITE-INTEGER-AP-PROVENANCE.json').write_text(json.dumps(new,indent=2),encoding='utf-8')
print(json.dumps(dict(module=name,source_lines=[new['original_start_line'],new['original_end_line']],
 original_sha256=new['original_sha256'],certified=False)))
