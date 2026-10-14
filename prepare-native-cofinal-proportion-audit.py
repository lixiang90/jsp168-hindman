from pathlib import Path
import json,re

prefix='round-native-cofinal-proportion'
source=Path('round-native-real-rough-proportion-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='round-native-real-rough-proportion'","PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-residual-proportion'","OLD='round-native-real-rough-proportion'")
source=source.replace("BASELINE='round-native-real-rough-proportion-baseline.json'","BASELINE='"+prefix+"-baseline.json'")
source=source.replace("MODULES=['Hindman168/ResidualRealBoxGeometry.lean','Hindman168/NativeRealResidualLargeEvent.lean','Hindman168/NativeRealResidualRoughProportion.lean','Hindman168/NativeRealOriginalRoughProportion.lean']",
 "MODULES=['Hindman168/RoughCofinalDataExtension.lean','Hindman168/RoughCofinalStrictSelection.lean','Hindman168/NativeCofinalRoughProportion.lean']")
source=source.replace("read('round-native-real-rough-proportion-lakefile-before.toml')","read('"+prefix+"-lakefile-before.toml')")
components=[
 'Actual scale data on a strictly increasing sieve-width sequence now extend to ALL natural widths with EXACT values at each observed width and genuine inherited real-power growth. Only scales are extended; no fictitious source/model/modulus/bad sample is introduced at unobserved widths.',
 'For ANY cofinal natural width sequence, a frequent failure yields a subsequence strictly increasing in BOTH original sample indices and ACTUAL widths. Genuine eventual/limit transfer from those subsequences discharges any monotonicity or injectivity restriction on the original sequence.',
 'UNCONDITIONAL original/residual REAL-box non-strict complex rough-fraction convergence now holds along ANY actual w->infinity sequence, including repetitions/nonmonotonicity. Smooth prime bounds, primorial divisibility and rough coprimality use the ACTUAL sieve width W(k), never the sequence index k. Native family members, raw sources, q/a and all varying sampling witnesses are retained.'
]
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original/residual complex non-strict rough exceptional-proportion convergence is proved for arbitrary REAL boxes and ANY actual cofinal sieve-width sequence, with simultaneous nonempty samples, literal source/event composition and common finite-native-family budgets WITHOUT coprimality. Remaining: actual master/source/conditional-probability application including uniform bounded normalized-scale variation, separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse, full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author-side checking, not independent replay or external peer review.\n\n'
 'Primary source says ALONG ANY SEQUENCE w->infinity. Earlier native\n'
 'proportion statements identified sequence index with sieve width;\n'
 'merely composing their limits would not check actual smoothness/primorial\n'
 'conditions on differently indexed or repeated widths. This gap is closed.\n\n'
 'For strictly increasing actual W(k), the largest observed index before\n'
 'each natural width is given by an actual finite Nat.findGreatest.\n'
 'Strict monotonicity proves k<=W(k), the selected index at W(k) is EXACTLY k,\n'
 'and the selector tends to infinity. Original scale/power-ratio limits\n'
 'therefore extend to all widths. NO raw source, modulus, model or bad\n'
 'sample is fabricated at an unobserved width. The unconditional\n'
 'uniform theorem is applied to the extended scales, then evaluated at\n'
 'the actual observed widths with the original arbitrary raw inputs.\n\n'
 'The resulting strict-cofinal native theorem uses prime<=W(k),\n'
 'primorial(W(k))|modulus(k) and actual rough coprimality, not width=k.\n'
 'Exact sample values recover original Scale(k), Z(k) before all\n'
 'source/geometry/denominator arguments. All actual family/source/q/a\n'
 'and non-strict complex real-box event quantifiers survive.\n\n'
 'An arbitrary cofinal W may repeat/oscillate. Any frequent failure\n'
 'admits an actual recursive subsequence with BOTH strictly increasing\n'
 'indices and widths: cofinal width thresholds intersect the frequent\n'
 'bad set, and the successor choice exceeds both previous bounds.\n'
 'The generic eventual/limit-transfer theorem proves convergence on\n'
 'the original arbitrary sequence from those genuine subcases. Its\n'
 'subsequence premise is discharged by the already proved native\n'
 'strict-cofinal comparison, not supplied as an analytic oracle.\n'
 'Original source degree/log identities and all actual sampling\n'
 'hypotheses restrict to that actual subsequence without alteration.\n\n'
 'NativeNilmanifoldData was inspected: it contains legitimate finite\n'
 'model/Lie group/nilpotence/lattice/compatible metric data, with no\n'
 'inverse, no-bad or rough-comparison field. StrongConjecture was\n'
 're-read and remains the original full positive distinct rapidly\n'
 'separated simultaneous monochromatic FS/FP target; it is UNPROVED.\n\n'+remaining+'\n',encoding='utf-8')
print(json.dumps(dict(prefix=prefix,new_modules=3,new_theorems=12,full_target_proved=False)))
