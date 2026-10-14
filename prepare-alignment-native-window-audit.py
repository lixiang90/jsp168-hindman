from pathlib import Path
import re

prefix='round-alignment-native-window'
old='round-native-conditional-proportion'
source=Path(old+'-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='"+old+"'", "PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-cofinal-proportion'", "OLD='"+old+"'")
source=source.replace(old+'-baseline.json',prefix+'-baseline.json')
source=source.replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
modules=['Hindman168/PowerDominationRealRatios.lean','Hindman168/AlignmentNativeReferenceGrowth.lean','Hindman168/AlignmentNativeWindowSampling.lean','Hindman168/AlignmentNativeWindowUniform.lean','Hindman168/ActualSelectorUniformity.lean','Hindman168/AlignmentNativeWindowAllAnchors.lean']
source=re.sub(r'^MODULES=.*$', 'MODULES='+repr(modules),source,count=1,flags=re.M)
components=[
 'Genuine natural-power domination now yields ALL positive REAL-exponent paper ratios with explicit positive denominators. Actual raw master retained-product reference scales and typical exposed factor scales discharge native scale-growth hypotheses from MasterParameterConditions.',
 'The ACTUAL binary dyadic residue window and its uniform factor law are exactly the roughDyadicResidueSteps analytic sampling set/law. Actual smooth master powers and original supported rough units derive every prime support, primorial divisibility and residue-unit premise, without coprimality of retained q.',
 'The proved finite-native-family analytic budget now yields actual exposed-window variable-scale event caps with master scale/arithmetic/density/normalization hypotheses discharged. Uniformity is strengthened to ALL actual supported typical anchors, retained subsets and tail directions by a proved selector argument using genuine positive typical-event mass. No input rough-proportion/analytic bound or anchor-dependent cutoff remains; actual polynomial/log packets and scale geometry remain explicit.'
]
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Native rough proportions, real/cofinal/bounded-scale comparison and actual master-window caps now have fully derived growth/arithmetic and uniformity over all supported typical anchors. Actual posterior Fubini/union domination is proved. Remaining: construct actual Alignment orbit-array joint native logarithmic polynomial packets, degree bounds, retained coarse residue and scale-range/event inclusion; instantiate the conditional fiber caps and synthesize Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse; full cube synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author checking, not independent replay or external peer review.\n\n'
 'Growth review: PowerDominates is natural-power little-o, whereas the\n'
 'original rough proposition asks for every positive REAL exponent. For\n'
 'S>=1 the real power a is bounded by the natural power ceil(a); positive\n'
 'fixed multiples of that natural power are eventually below Z. The exact\n'
 'positive rpow denominator then gives any lower ratio threshold. This\n'
 'does not assume the desired rough conclusion. Actual raw master retained\n'
 'products inherit PowerDominates from the previously proved master growth;\n'
 'division by fixed positive Kref preserves every real ratio. Typical binary\n'
 'cutoff conditions give actual factor-scale divergence using the proved\n'
 'dyadic-residue density ratio and positive residue modulus >=1.\n\n'
 'Sampling review: equality of finite windows is extensional membership\n'
 'equality, including half-open endpoints, casts and modulo representatives.\n'
 'Its exact uniform-law equality has no rounding/normalizer approximation.\n'
 'For w>=1 the actual modulus F.modulus(w)*primorial(w)^w is positive,\n'
 'smooth and divisible by the actual primorial. The original raw support\n'
 'gives genuine rough coprimality, which transfers to x mod modulus.\n'
 'These statements impose no gcd between retained q and removed factor t.\n\n'
 'Actual analytic cap review: the native finite-family reference bound\n'
 'is obtained from its PROVED unconditional theorem, using the derived\n'
 'master real-power growth. Actual master density discharges the selected\n'
 'ratio threshold. The real residual event retains literal Q, source log\n'
 'polynomial packet, q/a, all compatible samples and varying normalized\n'
 'geometry. Exact count/event conversion gives the actual window cap.\n'
 'Polynomial packet degree/log identity and bounded scale-range are the\n'
 'genuine remaining raw source/geometry class inputs, not assumed caps.\n\n'
 'Uniformity review: a theorem valid for every actual selector is promoted\n'
 'to one eventual cutoff before ALL actual anchors/subsets/directions.\n'
 'Positive typical-event probability supplies genuine valid raw anchors\n'
 'at all large widths. The selector chooses a failing valid object when\n'
 'one exists, otherwise a valid actual object. Defaults occur only before\n'
 'eventual validity; no analytic/source/model truth is asserted for them.\n'
 'The proved native selector theorem contradicts any remaining failure.\n'
 'Empty tails are treated vacuously, never by inventing a direction/model.\n'
 'This discharges anchor-dependent cutoff quantifiers, not just fixed\n'
 'anchor convergence. Conditional posterior factors remain dependent.\n\n'
 'The original target and actual interval correlation-inverse proposition\n'
 'were re-read. StrongConjecture and HasNativePeriodicIntervalInverse are\n'
 'still unproved. Actual Alignment polynomial packets and fiber event\n'
 'instantiation remain work; this is not a proof of final Alignment.\n'
 'No new axiom/sorry/unsafe/native shortcut or instance/option/structure\n'
 'bypass is used. Prior proof source hashes and axiom sets must remain exact.\n\n'+remaining+'\n',encoding='utf-8')
print(prefix)
