from pathlib import Path
import re

prefix='round-alignment-native-source'
old='round-alignment-native-window'
source=Path(old+'-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='"+old+"'", "PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-conditional-proportion'", "OLD='"+old+"'")
source=source.replace(old+'-baseline.json',prefix+'-baseline.json')
source=source.replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
source=source.replace('2026-10-13','2026-10-14')
modules=['Hindman168/SingletonChartNativeExponential.lean','Hindman168/AlignmentArrayNativeCoordinates.lean','Hindman168/NativeVectorPolynomialSource.lean','Hindman168/AlignmentExposedNativeVectorPolynomial.lean','Hindman168/RoughVectorMvSubstitution.lean','Hindman168/RoughRemovedFactorPolynomial.lean','Hindman168/AlignmentExposedNativeSource.lean','Hindman168/AlignmentRemovedFactorNativeSource.lean']
source=re.sub(r'^MODULES=.*$', 'MODULES='+repr(modules),source,count=1,flags=re.M)
components=[
 'The genuine array coefficient logarithm is now identified with the native global logarithm by the actual singleton-chart differential, original exponential ray subgroup law and ODE uniqueness. The actual array nilmanifold retains original group, lattice, step and constructed compatible metric, with arbitrary original-model universes and actual small finite array indices.',
 'Actual exposed scalar joint-log polynomials now assemble in a fixed basis into a vector polynomial of the same original uniform degree. Exposure-key freezing is proved. Its native all-real exponential source has a PROVED joint-log identity and exact equality to ORIGINAL actual cube arrays at every permitted sampling point; unsampled extension values cannot substitute for sampled source identity.',
 'A genuine linear change of polynomial variables isolates ONE removed factor and literally freezes all others, preserving total degree and every spatial variable. The source ignores changes to the deleted factor dummy frozen value. The actual source sample identity and its normalized spatial-residue polynomial degree/all-real native logarithm packet are proved outright, without supplied polynomial/log or rough-comparison oracles.'
]
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Actual single-model exposed/removed-factor native sources, uniform degree bounds, normalized residual log packets and original sampled-array identities are proved, together with earlier unconditional native rough proportions, all-anchor master-window caps and actual posterior Fubini domination. Remaining: assemble finite JOINT native source/observable families and exact spatial coordinate reindexing; derive actual retained coarse residue, bounded scale-range and bad-event inclusion; instantiate conditional fiber caps and synthesize Alignment; separately prove arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse; full cube synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-14. Partial overall coverage.\n'
 'Author checking, not independent replay or external peer review.\n\n'
 'The pinned source rough residual corollary requires a true jointly\n'
 'logarithmically polynomial native source, and Alignment supplies actual\n'
 'exposed polynomial arrays. A scalar coefficient log cannot simply be\n'
 'renamed as the native global log. This missing connection is now proved.\n\n'
 'Singleton-chart differential is genuinely identity in the original normed\n'
 'model. The original exponential arrays obey the ray subgroup law at ALL\n'
 'integer array evaluations, which faithfully determine the actual group.\n'
 'Zero velocity and ODE uniqueness identify the original coordinate\n'
 'homeomorphism with native exponential; native log is its genuine inverse.\n'
 'The coefficient/log linear equivalence therefore gives the actual native\n'
 'coordinate relation, with no compatibility assumption.\n\n'
 'The old array nilmanifold wrapper tied its index and model universes.\n'
 'The new genuine construction allows actual small finite array indices\n'
 'and ANY original native model universe: it reuses the same original\n'
 'array Lie group, discrete pointwise lattice, compact quotient, step and\n'
 'compatible metric recipe. Explicit class bindings contain only those\n'
 'already proved canonical structures; no custom instance declaration or\n'
 'compiler option is introduced. Typed coefficient/value interfaces expose\n'
 'the same actual groups/modules, not replacement models.\n\n'
 'The fixed finite basis of the actual native array model assembles the\n'
 'EXISTING genuine scalar exposed joint-log polynomials into a finite list\n'
 'vector polynomial. Basis reconstruction proves all coordinates together;\n'
 'the uniform degree ((s*s+1)^(s+1))*max(1,T.card) survives, independent of\n'
 'coefficients/w/samples. Genuine exposure-key equality freezes the source.\n'
 'The exponential extension is real-log polynomial by the proved native\n'
 'log/exponential identity, and at every permitted original cube sample\n'
 'its value is exactly the original canonical cube array. This latter\n'
 'identity is essential and is proved, not inferred from extension values.\n\n'
 'Linear substitution leaves spatial variables untouched, exposes removed\n'
 'factor j as parameter none, and replaces ALL other factors by their\n'
 'literal frozen values. Total degree cannot increase. Genuine variable\n'
 'evaluation gives Function.update of exactly that parameter. The dummy\n'
 'frozen value at j is ignored; update invariance is proved. Explicit\n'
 'DecidableEq binders only reconcile actual Fin equality enumeration with\n'
 'generic updates; all such equalities are proved without new instances.\n'
 'The actual single-factor native source is then assembled from this\n'
 'restricted polynomial. Its sample identity uses the actual cube vector\n'
 'evaluation and update_eq_self, retaining original hypotheses. Spatial\n'
 'x=a+q*y composition gives normalized polynomial and all-real log packet\n'
 'at the original degree; q and a stay fixed while removed factor varies.\n'
 'No gcd(q,t), source/log packet or comparison bound is assumed.\n\n'
 'Remaining source work is accurately separated: heterogeneous finite\n'
 'JOINT array model/observable synthesis, coordinate indexing, actual\n'
 'retained residue, geometry range, bad-event inclusion and conditional\n'
 'application. The GTZ interval correlation inverse is still independent\n'
 'and unproved. No completed Alignment or StrongConjecture is claimed.\n'
 'Preserve all registered old proofs, axioms and main pins; no sorry,\n'
 'custom axiom, native/unsafe shortcut or option/instance bypass.\n\n'+remaining+'\n',encoding='utf-8')
print(prefix)
