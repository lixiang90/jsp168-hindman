from pathlib import Path
import json, re

old = 'round-alignment-complete-cube-face-probability'
prefix = 'round-native-cylinder-diagonal'
modules = [
    'AlignmentJointNativeSlotSeparation',
    'AlignmentJointNativeCylinderAlgebra',
    'ContinuousCylinderListRepresentation',
    'AlignmentJointNativeCylinderLists',
    'AlignmentJointNativeCompleteCylinderPool',
    'ContinuousCylinderMeanTransfer',
    'AlignmentJointNativeCylinderDetection',
    'CountablePositiveEventDiagonal',
    'AlignmentCompleteCubeCountableSelection',
    'AlignmentJointNativeCylinderPresentation',
]
components = [
    'ALL original integer-slot coset evaluations jointly determine the ACTUAL native array/product quotient by the genuine pointwise and product lattice. Distinct native quotient points have an actual original component/slot witness; no fixed finite lattice-quotient embedding is assumed.',
    'Actual Lipschitz component cylinder generators form a star-closed family and separate native quotient points. Stone-Weierstrass supplies uniform approximation of EVERY native continuous test; exact finite coefficient/list representations retain all original slots and observers. Compact complete numerical test classes admit ONE finite cylinder observer pool and strict positive coefficient budget before sources, boxes, residues and samples.',
    'Exact cylinder-list finite-mass means and weighted errors prove one finite ORIGINAL cylinder-product detector list and one positive tolerance control EVERY actual native bounded/Lipschitz test. Both arbitrary empirical sets/maps and their literal normalization are retained, including zero means on empty sets. This is a complete native test reduction, not yet the actual native all-face failure probability theorem.',
    'Genuine finite-prefix failure mass tends to zero. Positive prescribed-event mass and slow-stage selection supply ONE supported sample sequence satisfying EVERY fixed enumerated condition and arbitrary additional eventual stage requirements. Actual original all-complete-reading-cube failure limits instantiate this along ANY cofinal width sequence, including repeated/nonmonotone widths and variable finite cube dimensions. All original modulus/geometry/numerical/slot conditions may be enumerated before the later sequence-selected period.',
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'ALL original integer-slot cylinder tests now separate the actual native quotient, approximate every native numerical test with fixed finite budgets and detect arbitrary empirical discrepancies. '
    'Actual original complete finite-reading cube conditions now admit one countable supported positive-event selection along any cofinal width sequence, compatible with additional stage requirements. '
    'Remaining: instantiate finite native cylinder products by duplicated ORIGINAL component/slot observations with exact original own-face sample maps and common numerical budgets, and derive actual native all-face probability vanishing/countable selection; '
    'then original local cube/Haar law with sequence-selected period, limit-before-relative-box limit, coset face symmetry and full Alignment; '
    'separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse with sufficient native step for the actual finite degree list; final positive distinct rapidly separated monochromatic FS/FP. '
    'Author Lean checking is not independent kernel replay or external peer review. No other-component invariance, unexposed-factor-dependent formula uniformity or explicit delta-power law is claimed. '
    'Repaired source slab estimate is not an unavoidable obstruction. Public repository/PR/prize milestone not reached.')

baseline = Path('verification-manifest.json').read_bytes()
Path(prefix+'-baseline.json').write_bytes(baseline)
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
source = Path(old+'-audit.py').read_text(encoding='utf-8').replace(old,prefix)
source = re.sub(r'^OLD=.*$', 'OLD='+repr(old), source, flags=re.M)
source = re.sub(r'^MODULES=.*$', 'MODULES='+repr(['Hindman168/'+m+'.lean' for m in modules]), source, flags=re.M)
source = re.sub(r'^COMPONENTS=.*$', lambda _: 'COMPONENTS='+repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING=.*$', lambda _: 'REMAINING='+repr(remaining), source, flags=re.M)
source = source.replace("return ['Hindman168.'+n for ds in decls().values() for _,n in ds]+EXTERNAL", "return [('Hindman168.FiniteMass.' if p.endswith('/CountablePositiveEventDiagonal.lean') else 'Hindman168.')+n for p,ds in decls().items() for _,n in ds]+EXTERNAL")
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-mathematical-review.txt').write_text('''JSP-000168 / Erdos #172 -- author mathematical review, 2026-10-14
Verdict: Partial overall coverage; PROGRESS. StrongConjecture UNPROVED.
Goal ACTIVE; no unavoidable obstruction established.
Author checking is not independent kernel replay or external peer review.

Primary source: OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
08_alignment.tex, especially original marginal face comparison (lines 550-575),
the countable diagonal and period (577-611), and intrinsic readings (663 ff).
The retained original paper sections are compared to pinned Git objects.

1. Point separation. Representatives a,b are equal modulo the actual native
product lattice iff a^-1*b lies in that lattice. Product-lattice membership is
componentwise; array-lattice membership is membership at EVERY integer slot.
QuotientGroup.eq gives precisely the equality of corresponding original cosets.
No normal-lattice assumption is used. A finite Lie determining evaluation list
is NOT asserted to determine lattice cosets. Empty products are genuine and
the resulting quotient has no distinct points requiring a fake slot witness.

2. Dense tests. Original component quotients use their constructed native metric
topologies. Lipschitz distance tests separate original slot values; composition
with actual continuous coset evaluations gives continuous native cylinder tests.
Numerical Lipschitz bounds on the slot projection are NOT inferred. The family
is star-closed by complex conjugation. The generated unital complex star algebra
separates points, so compact Stone-Weierstrass proves density. Every element
is exactly a finite complex linear combination of finite products of the
ORIGINAL generator family; conjugates are returned to that family by star
closure. Finite lists preserve repetitions, zero coefficients and empty products.

3. Uniformity. The entire native B-bounded L-Lipschitz class is compact. A finite
cover and dense cylinder approximation produce ONE finite approximant list.
All retained original observers are included in one finite pool, and
R=1+sum of coefficient norms bounds every retained coefficient list STRICTLY.
Outside the retained approximant list empty fallback lists receive NO equality
or approximation claim. Observers, slots, approximants and R are selected
BEFORE any empirical samples or source formulas.

4. Means and detection. Actual finite signed-mass means are exactly linear in
the retained cylinder coefficients. Weighted triangle bounds need no measure
positivity. For original uniform means, sup-error at eta/4 controls EACH mean,
also when a sample set is empty. Absence of a cylinder product discrepancy at
eta/(2R) bounds every term weakly by that value; the STRICT coefficient sum
bound implies a STRICT eta/2 approximant discrepancy. Triangle bounds contradict
an eta complete-test discrepancy. Thus a FIXED finite product detector list
works for every complete native numerical test and any two empirical sets/maps.
This generic reduction DOES NOT supply the original source maps, face action,
or the detector probability cap. Those must be explicitly instantiated.

5. Countable choice. For each fixed initial list, original nonnegative event
masses obey the finite union bound and converge to zero. Therefore failure
mass is eventually below the prescribed positive event lower bound beta.
Support-restricted event monotonicity forces a supported good sample in that
event. The proved slow-stage theorem chooses an increasing-in-limit stage
from these fixed-list thresholds; no unjustified growing-index convergence
is asserted. At invalid initial indices only an arbitrary fallback value is
used; membership and estimates are asserted only EVENTUALLY. Every fixed
enumerated condition is eventually satisfied on the SAME sample sequence.
Arbitrary extra eventual stage obligations can be kept in the construction.

6. Original application. The original raw-law failure theorem gives the
complete finite-reading cube event, uniformly over all endpoints/residues,
bounded/Lipschitz tests, own pairs and zero/one vertex profiles. It is
instantiated separately for every enumerated condition, then pulled back by
any actual W(j)->infinity. Width W(j), not index j, determines primorial,
cutoff, exposure key and the source formula. Source formula selection may
depend on width/exposure key but never unexposed factors. Dimensions may
vary by condition. Every fixed positive modulus may be included before
the later local-law period is chosen. The theorem does not itself prove
a native local Haar limit or assert that the later period already exists.

7. Coverage. These nine modules close original slot separation, native test
density/finite detection and the actual complete finite-reading countable
selection. The native detector products still need exact duplicated-component
original source/face identities and actual all-face probability caps. Native
Haar local laws, coset face symmetry, full Alignment, the separate arbitrary
interval Gowers LINEAR nilsequence inverse and final positive distinct
rapidly-separated monochromatic FS/FP target remain unproved. A repaired
earlier source slab estimate is not an unavoidable obstruction. No full
formalization, publication milestone or award eligibility is claimed.

Remaining proof work:
'''+remaining+'\n',encoding='utf-8')
print(prefix, len(modules), 'modules')
