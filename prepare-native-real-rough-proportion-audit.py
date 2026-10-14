from pathlib import Path
import json,re

prefix='round-native-real-rough-proportion'
source=Path('round-native-residual-proportion-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='round-native-residual-proportion'","PREFIX='"+prefix+"'")
source=source.replace("OLD='round-rough-residual-sampling'","OLD='round-native-residual-proportion'")
source=source.replace("BASELINE='round-native-residual-proportion-baseline.json'","BASELINE='"+prefix+"-baseline.json'")
source=source.replace("MODULES=['Hindman168/NativeResidualSource.lean','Hindman168/NativeResidualLargeEvent.lean','Hindman168/NativeResidualRoughProportion.lean']",
 "MODULES=['Hindman168/ResidualRealBoxGeometry.lean','Hindman168/NativeRealResidualLargeEvent.lean','Hindman168/NativeRealResidualRoughProportion.lean','Hindman168/NativeRealOriginalRoughProportion.lean']")
source=source.replace("read('round-native-residual-proportion-lakefile-before.toml')","read('"+prefix+"-lakefile-before.toml')")
components=[
 'Arbitrary original REAL-box endpoints now have EXACT residual integer endpoints ceil((x-a)/q). Actual positive-q affine order/congruence and ceil identities prove this without numerical approximation or a coprimality premise. Original/normalized boxes retain the exact same samples.',
 'The source real-power growth now proves ONE uniform real-box sampling threshold. EVERY permitted original coarse q-class and compatible fine q*t-class is genuinely NONEMPTY at every actual dyadic step thereafter. This holds simultaneously over arbitrary endpoints and finer residues; no nonempty assumption is put into the original real-box event.',
 'UNCONDITIONAL original and residual rough exceptional fractions now tend to zero for arbitrary REAL spatial boxes, non-strict complex discrepancy and varying actual finite native-family members/raw sources/retained factors. Only fixed harmless geometry constants change under ceil rounding; eta, actual sampling laws and original varying-witness quantifiers are retained. Retained q/a remain independent of the removed t.'
]
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original/residual complex non-strict rough exceptional-proportion convergence is proved for arbitrary REAL boxes, with actual simultaneous nonempty sample proofs, literal source/event composition and common finite-native-family budgets WITHOUT coprimality. Remaining: cofinal w-index bridge and actual master/source/conditional-probability application (including uniform bounded normalized-scale variation), separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse, full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author-side checking, not independent replay or external peer review.\n\n'
 'Primary route: pinned Section 6 original/residual rough-step comparison.\n'
 'The old integer-box/nonempty-event formulation required an application bridge.\n'
 'This round explicitly closes that gap for arbitrary real box endpoints.\n\n'
 'For actual q>0, the exact residue-index endpoint at ceil(x) equals\n'
 'ceil((x-a)/q). The proof compares all integer upper cuts using the original\n'
 'first-residue-point characterization and exact positive-q division. This is\n'
 'an equality, not a discarded-tail estimate or a sampled-source inference.\n\n'
 'The normalized real box with side >=c*Z yields an integer side >=c*Z/2.\n'
 'The true ceil endpoint bounds yield location/width constants 2*(C+1).\n'
 'The changes are fixed geometry constants, independent of every raw box,\n'
 'source, q/a, removed t and compatible finer residue. Original eta and the\n'
 'complex discrepancy are unchanged; exact sampling laws are retained.\n\n'
 'Actual Z/S -> infinity (from the source power ratios) and S->infinity give\n'
 'one threshold with S,Z>=1, c*Z>=2 and c*Z>=8*S. Every actual dyadic t<2*S\n'
 'is positive and 4*t<=c*Z. Thus every normalized integer t-class is\n'
 'nonempty. Exact affine images give BOTH original q and q*t samples\n'
 'nonempty for every compatible fine residue, WITHOUT coprimality.\n'
 'No nonempty premise is included in the original real-box large-event\n'
 'definition; nonemptiness is proved at the uniform eventual threshold.\n\n'
 'The original real-box event uses the actual ceil endpoint samples and\n'
 'non-strict complex error. Exact event inclusion maps it to the already\n'
 'proved residual comparison. One fixed threshold precedes all raw sources\n'
 'and retained q/a across the fixed finite native family. Actual family\n'
 'members/source coefficients and q/a may vary with w.\n\n'
 'Taking retained q=1, a=0 gives the true ORIGINAL rough-step event. The\n'
 'coarse class equals exactly the full integer points of the real box,\n'
 'and the literal residual source equals Q at EVERY real input. The raw\n'
 'original polynomial supplies the source identity without an extra\n'
 'normalized-source or inverse premise. No false empty-family model\n'
 'existence, fixed-box restriction or zero-denominator substitution occurs.\n\n'
 'C>=0 is weaker than the manuscript C>0 requirement. Geometry results\n'
 'retain this original harmless assumption; no compiler or linter option\n'
 'is suppressed. Full-goal completion is not inferred from these results.\n\n'+remaining+'\n',encoding='utf-8')
print(json.dumps(dict(prefix=prefix,new_modules=4,new_theorems=11,full_target_proved=False)))
