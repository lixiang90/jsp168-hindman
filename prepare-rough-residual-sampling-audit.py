from pathlib import Path
import json,re

prefix='round-rough-residual-sampling'
source=Path('round-native-finite-proportion-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='round-native-finite-proportion'","PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-original-proportion'","OLD='round-native-finite-proportion'")
source=source.replace("BASELINE='round-native-finite-proportion-baseline.json'","BASELINE='"+prefix+"-baseline.json'")
source=source.replace("MODULES=['Hindman168/NativeFiniteRoughProportion.lean']","MODULES=['Hindman168/RoughNestedResidueSampling.lean']")
source=source.replace("read('round-native-finite-proportion-lakefile-before.toml')","read('"+prefix+"-lakefile-before.toml')")
components=[
 'The actual nested residual-step integer/box image laws x=u+q*y now retain ORIGINAL arbitrary box endpoints and the true finer step q*t WITHOUT any coprimality between q and t. Every compatible finer residue has an actual integer representative, with exact congruence equivalence.',
 'Actual normalized uniform laws push exactly to the original coarse q-class and finer q*t-class. The COMPLEX discrepancy identity retains the same observable and actual samples, including empty-set equality cases. This supplies the arithmetic/sampling interface of the source residual-step corollary, not yet its full native source/master/conditional-probability application.',
 'The prior original complex non-strict rough-proportion convergence and ONE common fixed-finite-native-family budget remain proved under unchanged source hashes, main pins and transitive axiom sets.'
]
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original native complex non-strict rough exceptional-proportion convergence, ONE uniform fixed-finite-family budget, and exact ORIGINAL residual q/q*t sampling laws WITHOUT coprimality are proved. Remaining: literal native residual-source/event composition and actual master/source/conditional-probability application with source-interface/cofinal-index/nonempty-sample bridges, separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse, full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
assert "MODULES=['Hindman168/RoughNestedResidueSampling.lean']" in source
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author-side checking, not independent replay or external peer review.\n\n'
 'Source Section 6 residual-step corollary explicitly disallows an extra coprimality\n'
 'assumption between the retained q and removed t. Existing unrelated CRT intersection\n'
 'lemmas require coprimality and cannot be substituted for this nested-class law.\n\n'
 'The actual signed residue endpoints reconstruct the original first q-class point\n'
 'at each original endpoint. Under x=u+q*y, an actual t-class becomes the q*t-class\n'
 'with residue u+q*v. Finer congruence implies the coarse q-congruence, so the exact\n'
 'coarse endpoint equivalences recover the ORIGINAL full box boundaries without tails.\n'
 'No modular inverse or gcd assumption is used. The scalar q is genuinely positive.\n\n'
 'Independent coordinate images give the full original box image. Injectivity\n'
 'of the positive-q affine map gives the exact uniform probability push. Both\n'
 'coarse and fine laws retain their actual empty/nonempty supports; equality\n'
 'is valid even for empty supports, with no invented probability mass.\n'
 'The complex expectation push proves an exact discrepancy identity for the\n'
 'SAME original arbitrary observable. Compatible arbitrary finer representatives\n'
 'are recovered by actual integer congruence witnesses, not by assuming divisibility.\n\n'
 'Retained u/q must be independent of the factor removed when these laws are\n'
 'composed with native joint polynomial sources. That composition and the\n'
 'conditional/master application are subsequent obligations, not claimed here.\n\n'+remaining+'\n',encoding='utf-8')
print(json.dumps(dict(prefix=prefix,new_modules=1,new_theorems=5,full_target_proved=False)))
