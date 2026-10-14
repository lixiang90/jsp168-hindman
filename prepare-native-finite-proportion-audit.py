from pathlib import Path
import json,re

prefix='round-native-finite-proportion'
source=Path('round-native-original-proportion-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='round-native-original-proportion'","PREFIX='"+prefix+"'")
source=source.replace("OLD='round-dense-fixed-length-block'","OLD='round-native-original-proportion'")
source=source.replace("BASELINE='round-native-residue-density-baseline.json'","BASELINE='"+prefix+"-baseline.json'")
source=re.sub(r"MODULES=\[.*?\]\nMODULES=\['Hindman168/'\+n\+'\.lean' for n in MODULES\]",
 "MODULES=['Hindman168/NativeFiniteRoughProportion.lean']",source,count=1,flags=re.S)
source=re.sub(r'EXTERNAL=\[.*?\]\nCOMPONENTS=', 'EXTERNAL=[]\nCOMPONENTS=',source,count=1,flags=re.S)
components=[
 'The actual original complex non-strict native rough-proportion theorem now has ONE positive ratio threshold and ONE eventual threshold simultaneous over EVERY member of a fixed finite family of legitimate native nilmanifolds. Genuine threshold monotonicity and finite sums/intersections precede all raw source coefficients, moduli, residues, boxes and observables. Empty families assert no fake model or character existence.',
 'The prior genuine finite Szemeredi closure, literal all-real source/ordinary degree transport, exact residue-index/ceil/cardinality geometry, real/complex non-strict event comparison and original rough-fraction convergence remain proved with all retained source hashes and axiom sets unchanged.'
]
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original native complex non-strict rough exceptional-proportion convergence and ONE uniform fixed-finite-family budget are proved on actual nonempty dyadic residue samples, using the attributed verified finite Szemeredi closure and unconditional native dimension induction. Remaining: actual master/source instantiation and source-interface/cofinal-index/nonempty-sample boundary bridges, separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse, full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
source=source.replace("read('round-native-residue-density-lakefile-before.toml')","read('"+prefix+"-lakefile-before.toml')")
source=source.replace("expected['lean_lib']=before['lean_lib']+[dict(name='OAI',srcDir='dependencies/openai-finite-szemeredi',globs=['OAI.**'])]", "expected['lean_lib']=before['lean_lib']")
source=source.replace("if f['path']!='lakefile.toml'","if f['path'] not in {'Hindman168.lean','Verification.lean'}")
source=source.replace("{'Hindman168.lean','Verification.lean','lakefile.toml'}","{'Hindman168.lean','Verification.lean'}")
source=source.replace("files += [dict(path=p,sha256=digest(p)) for p in MODULES]+dependency_files",
 "files += [dict(path=p,sha256=digest(p)) for p in MODULES]\n assert all(any(old['path']==dep['path'] and old['sha256']==dep['sha256'] for old in files) for dep in dependency_files)")
assert "MODULES=['Hindman168/NativeFiniteRoughProportion.lean']" in source
assert 'EXTERNAL=[]' in source
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'This is author-side checking, not independent replay or external peer review.\n\n'
 'The original rough-proportion bound is monotone in its required ratio threshold:\n'
 'raising R merely restricts eligible raw moduli, so the existing conclusion applies\n'
 'with the SAME raw source, dyadic residue set and existential bad-event law.\n'
 'No equality of arbitrary native filtration/model records is asserted.\n\n'
 'For each actual native datum in a fixed Fintype family, the unconditional original\n'
 'theorem provides Ri before all raw sources. The common R=1+sum Ri is positive,\n'
 'dominates every Ri and works after the finite intersection of eventual thresholds.\n'
 'The SAME eventual w works for every member; the family member and all raw source,\n'
 'modulus/residue/box/test inputs follow the common threshold.\n'
 'Empty families give a positive bound and vacuous universal property only;\n'
 'they do not manufacture a model, horizontal character or nonempty sample.\n\n'
 'All prior proof sources and registered transitive axiom sets remain unchanged.\n'
 'The same 42-module attributed finite Szemeredi dependency remains pinned;\n'
 'no new dependency or toolchain configuration is introduced.\n\n'+remaining+'\n',encoding='utf-8')
print(json.dumps(dict(prefix=prefix,new_modules=1,new_theorems=2,full_target_proved=False)))
