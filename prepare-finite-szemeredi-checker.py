from pathlib import Path

source=Path('check-openai-dense-progression-bounded.py').read_text(encoding='utf-8')
source=source.replace("records_path=base/'openai-dense-progression-bounded-results.json'",
 "records_path=base/'openai-finite-szemeredi-results.json'")
source=source.replace("records=json.loads(records_path.read_text(encoding='utf-8')) if records_path.exists() else {}",
 "records=json.loads((records_path if records_path.exists() else base/'openai-dense-progression-bounded-results.json').read_text(encoding='utf-8'))")
source=source.replace('@functools.cache\n', '''selected_targets={
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
''',1)
source=source.replace("base/'openai-dense-progression-bounded-logs'", "base/'openai-finite-szemeredi-logs'")
source=source.replace("'openai-dense-progression-bounded-progress.json'", "'openai-finite-szemeredi-progress.json'")
source=source.replace("selected_target_built='OAI.Combinatorics.Progressions.Results.Conclusions' in done,",
 "selected_target_built='OAI.Compatibility.FiniteIntegerAP' in done,\n  uniform_cyclic_target_built='OAI.Combinatorics.Progressions.FixedDensity.Conclusions' in done,\n  count_extraction_built='OAI.Combinatorics.Progressions.FixedDensity.CountExtraction' in done,")
assert "selected_targets={" in source
assert "selected_target_built='OAI.Compatibility.FiniteIntegerAP'" in source
Path('check-openai-finite-szemeredi.py').write_text(source,encoding='utf-8')
print('Prepared checker for the genuine finite Szemeredi theorem and off-diagonal extraction.')
