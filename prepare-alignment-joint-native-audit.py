from pathlib import Path
import re

prefix='round-alignment-joint-native'
old='round-alignment-native-source'
source=Path(old+'-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='"+old+"'", "PREFIX='"+prefix+"'")
source=source.replace("OLD='round-alignment-native-window'", "OLD='"+old+"'")
source=source.replace(old+'-baseline.json',prefix+'-baseline.json')
source=source.replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
modules=['Hindman168/NativeFinitePiData.lean','Hindman168/NativeFinitePiCoordinates.lean','Hindman168/NativeFinitePiPolynomial.lean','Hindman168/AlignmentJointExposedNativeSource.lean','Hindman168/AlignmentJointRemovedNativeSource.lean','Hindman168/NativeFinitePiCosetCoordinates.lean','Hindman168/AlignmentArrayNativeCosetEvaluation.lean','Hindman168/AlignmentJointNativeReadings.lean','Hindman168/BoundedComplexLipschitzObservables.lean','Hindman168/AlignmentJointMetricReadings.lean','Hindman168/AlignmentJointMetricProducts.lean','Hindman168/AlignmentJointNativeSampleReadings.lean']
source=re.sub(r'^MODULES=.*$', 'MODULES='+repr(modules),source,count=1,flags=re.M)
components=[
 'A genuine finite heterogeneous native product is constructed with literal component groups and product lattice, original nilpotency cutoff, smooth product chart and compatible quotient metric in arbitrary model universes. Native exponential/log coordinates and actual product-model vector-polynomial/source identities are proved; empty products are genuine empty products without invented component existence.',
 'The ACTUAL finite JOINT exposed and one-removed-factor native sources now retain all original groups, determining evaluations, bases, vertices and slot shifts. Common original degree, exposure freezing, all-real normalized residual log packets and exact simultaneous equality to ORIGINAL cube arrays are proved.',
 'Actual product-lattice coset projections and integer-slot evaluations are proved continuous in BOTH natural quotient and specified native metric topologies via proved topology equality. Original complex readings retain exact values and bounds. No projection or reading is assumed numerically Lipschitz.',
 'The ACTUAL fixed numerical bounded/Lipschitz complex input classes and their joint finite product reading families are proved compact. One finite Lipschitz approximant list and positive output bounds are chosen BEFORE every original observation in these classes. The native metric product test equals the ORIGINAL simultaneous component observations at every permitted cube sample.'
]
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Genuine finite heterogeneous JOINT native sources, common degree, all-real residual packets, exact sampled arrays/complex metric readings and unconditional uniform finite Lipschitz approximation of bounded test product families are proved. Earlier native rough proportions, all-anchor master-window caps and posterior Fubini domination remain verified. Remaining: exact spatial finite-coordinate reindexing; actual retained coarse residue and bounded normalized-box scale-range; approximation error/bad-event inclusion and actual conditional fiber application; face/cube/Alignment and countable diagonal synthesis; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse with sufficient step for the actual finite required degree list; final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-14. Partial overall coverage.\n'
 'Author checking, not independent replay or external peer review.\n\n'
 'The original Alignment paragraph takes finite products over targets and\n'
 'models/vertices/slot shifts, and needs the ACTUAL joint array source and\n'
 'its original simultaneous observations. Single-model samples alone do\n'
 'not certify this. The new joint construction and sample/read identities\n'
 'address that actual requirement; no narrowed final target is introduced.\n\n'
 'nativeFinitePiData uses the literal heterogeneous dependent product group\n'
 'and literal product lattice. Each original native exponential diffeomorph\n'
 'constructs the smooth product chart; actual lower central cutoff, discrete\n'
 'lattice and compact quotient are proved dependencies. Compatible metric\n'
 'is constructed from the retained original native recipe. Actual small\n'
 'finite labels coexist with ANY original model universe. No group/lattice/\n'
 'compactness or analytic field is replaced by a desired conclusion.\n'
 'Original component ray laws and singleton-chart ODE uniqueness give the\n'
 'native product exponential/log coordinates. Genuine linear coefficient\n'
 'insertion and finite list flattening preserve total degree and literal\n'
 'component evaluation. Empty products retain actual unit/zero semantics,\n'
 'without deriving existence of a component or inverse character.\n\n'
 'Joint exposed sources allow every original component group, finite\n'
 'determining evaluation, basis, vertex weight and slot shift to differ.\n'
 'The original common degree survives, with no coefficient bound. Actual\n'
 'exposure freezing and simultaneous original cube-array sample identities\n'
 'are proved, not inferred from values off the sampling sets. Restriction\n'
 'to one free removed factor leaves all spatial directions free and freezes\n'
 'all other factors. Updating the dummy frozen value at that factor changes\n'
 'nothing. Spatial residue normalization retains q/residue independently\n'
 'of the removed parameter, with no gcd(q,t) assumption, and supplies the\n'
 'original degree and ALL-REAL native joint log packet outright.\n\n'
 'Coset coordinates descend through the actual product and pointwise array\n'
 'lattices; no normality of the original lattice is required. Natural\n'
 'quotient continuity transports through the PROVED native metric topology\n'
 'identity. This establishes continuity, NOT a numerical spatial Lipschitz\n'
 'constant for projections or readings. Exact slot readings preserve\n'
 'original complex values, bounds and uniform differences.\n\n'
 'The bounded complex test class has its original numerical B/L bounds.\n'
 'Closed pointwise bounded values and uniform equicontinuity give actual\n'
 'Arzela-Ascoli compactness. Continuous pullback and finite pointwise\n'
 'multiplication give compactness of the ACTUAL entire product test family.\n'
 'Proved compact-space Lipschitz density and a finite cover produce one\n'
 'finite approximant list and positive common output bounds BEFORE each\n'
 'original input test. Source quotient compactness in its specified metric\n'
 'is transported from genuine native compactness, not assumed. Nothing\n'
 'claims pointwise compositions were already Lipschitz. Original sampling\n'
 'readout equals the product of original component nilsequence values\n'
 'at all genuine integer cube samples, including every vertex/slot shift.\n\n'
 'The original StrongWitness/StrongConjecture was re-read unchanged.\n'
 'Inverse call sites were reviewed: required Gowers degrees are in a FINITE\n'
 'dimension list or bounded by maskRowCountBound. A genuine GTZ proof must\n'
 'choose sufficient native step for that actual finite list; no universal\n'
 'inverse for incompatible arbitrary step/degree pairs is claimed. This\n'
 'inverse remains unproved, not a consequence of equidistribution.\n\n'
 'Remaining geometry/coordinate/bad-event and conditional source application\n'
 'are explicit; this round is not a completed Alignment or Hindman theorem.\n'
 'All prior registered proofs and axiom sets must remain exact. No custom\n'
 'axiom/sorry/native/unsafe shortcut, new instance declaration or compiler\n'
 'option bypass is used. Local bindings are only genuine proved structures.\n\n'+remaining+'\n',encoding='utf-8')
print(prefix)
