from pathlib import Path
import json,re

prefix='round-native-residual-proportion'
source=Path('round-rough-residual-sampling-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='round-rough-residual-sampling'","PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-finite-proportion'","OLD='round-rough-residual-sampling'")
source=source.replace("BASELINE='round-rough-residual-sampling-baseline.json'","BASELINE='"+prefix+"-baseline.json'")
source=source.replace("MODULES=['Hindman168/RoughNestedResidueSampling.lean']",
 "MODULES=['Hindman168/NativeResidualSource.lean','Hindman168/NativeResidualLargeEvent.lean','Hindman168/NativeResidualRoughProportion.lean']")
source=source.replace("read('round-rough-residual-sampling-lakefile-before.toml')","read('"+prefix+"-lakefile-before.toml')")
components=[
 'ACTUAL native residual sources Q(t,a+q*y) and ordinary-degree-preserving vector polynomials are constructed by literal spatial-affine substitution, leaving the removed parameter unchanged. Their logarithmic identities hold at EVERY real input; retained q/a are fixed while t varies.',
 'Original non-strict complex residual q/q*t bad events with ANY compatible finer representative now map to original normalized bad events, with EXACT complex discrepancy and genuine original/normalized sample cardinalities. All existential varying boxes/residues/observables are retained; NO coprimality between q and t is assumed.',
 'UNCONDITIONAL residual rough-proportion bounds and convergence are proved from the actual source normalization and prior unconditional comparison. The normalized-only logarithmic polynomial premise matches the manuscript, and actual raw sources derive it by a proved constructor. ONE budget precedes retained q/a and every raw source/sampling datum, works across a fixed finite native family and permits the ACTUAL family member, q/a and source coefficients to vary with w. No same-comparison/inverse/production premise remains.'
]
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original and residual native complex non-strict rough exceptional-proportion convergence, literal residual source/event composition, common fixed-finite-family budgets and exact original sampling laws WITHOUT coprimality are proved. Remaining: actual master/source/conditional-probability application and source-interface/cofinal-index/real-box/nonempty-sample bridges, separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse, full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author-side checking, not independent replay or external peer review.\n\n'
 'Primary route: pinned Section 6 residual-step corollary. q/a are fixed while t\n'
 'varies. The literal Option-parameter-preserving spatial substitution is built\n'
 'term by term, preserving the original ordinary total degree. Its vector\n'
 'evaluation proves the logarithmic source identity at EVERY real t,y.\n'
 'Source equality is not inferred from finite samples or coset equality.\n\n'
 'The residual bad event uses ORIGINAL box endpoints, the original coarse\n'
 'q-class and arbitrary compatible finer residue modulo q*t. Normalized\n'
 'endpoint geometry is the precise assumption in the source corollary.\n'
 'An actual integer compatible representative is chosen; exact nested class\n'
 'images and injectivity transfer the two actual sample cardinalities.\n'
 'The EXACT complex discrepancy law retains the original observable, metric,\n'
 'Lipschitz/sup bounds and eta >= norm event. The two samples remain genuinely\n'
 'nonempty. There is NO coprimality/modular-inverse/fixed-box assumption.\n\n'
 'The full uniform bound takes the literal normalized source logarithm identity\n'
 'as in the manuscript. It does NOT require an extra raw-polynomial premise.\n'
 'When a true raw joint polynomial is available, the raw-source wrapper actually\n'
 'constructs the normalized polynomial and its all-real identity.\n'
 'The normalized native source is literally Q(t,a+q*y), not an independently\n'
 'supplied model/production oracle. The complete analytic comparison is the\n'
 'already proved unconditional original rough-proportion theorem.\n\n'
 'Finite filter inclusion transfers the event count with the SAME exact original\n'
 'dyadic step denominator. One uniform ratio/eventual threshold precedes all\n'
 'retained q/a, raw source coefficients and varying bad-event witnesses, and\n'
 'works across every actual member of the fixed finite native family.\n'
 'The actual member may vary with w in the convergence theorem, using dependent\n'
 'original source/polynomial types. The strict positive count bound proves the\n'
 'denominator positive before division. Empty native families assert no models.\n\n'
 'The normalized common scale Z must satisfy the original real-power growth;\n'
 'instantiate Z=Z0/q for the source corollary. Further uniformity over conditioned\n'
 'parameters with varying normalized scales requires the actual master bounds\n'
 'or a proved selection argument and is NOT inferred from a fixed-scale theorem.\n'
 'Arbitrary real spatial box conversion, nonempty sampling and cofinal w-index\n'
 'interfaces remain explicit source application obligations.\n\n'+remaining+'\n',encoding='utf-8')
print(json.dumps(dict(prefix=prefix,new_modules=3,new_theorems=8,full_target_proved=False)))
