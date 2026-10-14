from pathlib import Path
import ast

PREFIX = 'round-native-rational-unit-inverse'
OLD = 'round-native-rational-original-coefficient-transport'
MODULES = [
    'Hindman168/NativeRationalFiniteInverseBudget.lean',
    'Hindman168/NativeRationalResidueInverseBudget.lean',
    'Hindman168/NativeRationalCharacterInverseInduction.lean',
    'Hindman168/NativeRationalFiniteCharacterInverseInduction.lean',
    'Hindman168/NativeRationalNonzeroFourierInverseInduction.lean',
    'Hindman168/NativeRationalLargeInverseInduction.lean',
    'Hindman168/FiniteComplexDiscrepancyAnchor.lean',
    'Hindman168/NativeRationalConstantDiscrepancyAnchor.lean',
    'Hindman168/MvBoundedLengthCoefficient.lean',
    'Hindman168/NativeRationalLargeToAllLengths.lean',
    'Hindman168/NativeRationalFullInverseInductionStep.lean',
    'Hindman168/NativeRationalUnitInverse.lean',
]
COMPONENTS = [
    'ACTUAL bounded-denominator/residue canonical child data now receive ONE positive full inverse character/grid/two-table budget BEFORE every raw source, from legitimate strictly smaller-nonlinearity IH. True rational residue filtrations retain exact kernel layers and strict natural nonlinearity drop. Output source weights transfer directly by layer equality, without asserting equality of arbitrary filtration records.',
    'Every ACTUAL valid character in the original finite pool now closes its genuine child UNIT signal to BOTH COMPLETE raw ORIGINAL coefficient tables and nonzero horizontal/grid/norm character under ONE budget, from strictly smaller-nonlinearity IH. Empty pools and invalid characters assert no geometry. Full original nonzero terminal-frequency branches for large N and all finite terminal frequencies assemble with the genuine zero-mode lower-degree branch.',
    'TRUE finite discrepancy selects an ACTUAL sample anchor with point discrepancy at least the original mean discrepancy. A genuine weighted constant native polynomial through that actual sample preserves this discrepancy at EVERY positive length. The already proved large-N induction step applied to that constant source yields a true original bounded nonzero horizontal character; bounded short original N and actual degree then bound ALL monomial and binomial rows. No separate horizontal-character existence theorem, supplied inverse or unproved small-N case is used.',
    'UNCONDITIONAL NativeRationalWeightedInverseStatement D L Unit is now PROVED for ALL actual native data/rational Lie filtrations by genuine strong degree induction and strong NATURAL nonlinearity induction. Both actual lower-degree children use degree-1; conjugated canonical same-degree children use STRICTLY smaller nonlinearity. Genuine degree-zero/one bases and ALL original positive sample lengths are covered. The theorem returns an actual ORIGINAL nonzero horizontal/grid/norm character and BOTH COMPLETE raw ORIGINAL coefficient tables. It is a one-variable fixed-data existential inverse, not the corrected multiparameter theorem, explicit delta-power laws or final FS/FP goal.',
]
REMAINING = (
    'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'The full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. '
    'The COMPLETE unconditional native rational-filtration Unit inverse is now proved, with true degree/natural '
    'nonlinearity induction, actual canonical finite-child budgets, all zero/nonzero original Fourier branches, '
    'all positive sample lengths, actual original nonzero horizontal/grid/norm character and BOTH COMPLETE '
    'raw ORIGINAL coefficient tables. No higher-degree inverse premise remains in that Unit theorem. '
    'Remaining: construct genuine native multivariable short-line sources and use the corrected equal-cube '
    'common-character/dense-direction/basepoint reconstruction to prove the full multiparameter inverse; '
    'then separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final '
    'StrongConjecture. Prior P/diagonal/bracket branches are retained; direct explicit source delta-power '
    'laws have not been certified by these fixed-data existential constants. Only true positive exponential '
    'lattice powers are used, not Exp(y) lattice membership. Author build/hash/axiom/source review is not '
    'independent kernel replay or external peer review. The repaired source slab estimate is not an '
    'unavoidable obstruction. Public repository/PR/prize milestone has not been reached.'
)
source = Path(OLD + '-audit.py').read_text(encoding='utf-8')
lines = source.splitlines(keepends=True)
replacements = dict(PREFIX=PREFIX, OLD=OLD, MODULES=MODULES, COMPONENTS=COMPONENTS, REMAINING=REMAINING)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name + ' = ' + repr(replacements[name]) + '\n']
source = ''.join(lines).replace(
    'complete original coefficient transport from actual constructed child coefficients, with uniform original character/grid/two-table budget; child IH, complete native inverse and final target remain open',
    'unconditional complete native rational-filtration Unit inverse with genuine degree/nonlinearity induction and all original positive lengths; corrected multiparameter inverse and final target remain open')
Path(PREFIX + '-audit.py').write_text(source, encoding='utf-8')
Path(PREFIX + '-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. Unconditional complete native Unit inverse is proved;
StrongConjecture is NOT proved. This is author-side mathematical/application
review and the usual Lean kernel build/axiom checks, not independent replay.

1. Genuine child budgets. Each canonical rational residue data set is constructed
from the original SAME model/group, conjugated lattice and proved compatible
quotient metric. The residue direction is in the actual rational span, including
dummy zero denominators in the finite bounding pool. Canonical layers equal
the actual kernel layers; true natural nonlinearity strictly decreases. The
only inverse premise in the step is universal strictly smaller-nonlinearity IH.
Every finite child budget is chosen BEFORE raw p/N. Full norm/grid/monomial/
binomial data are retained and the grid is proved again under larger budgets.

2. Good character selection. Geometry from the proven actual character budget
is fixed before raw M/p/N. Actual child source/observable/discrepancy and SAME
original Fourier signal are used. Source weights transfer directly from output
Km.layer=K0.layer to the canonical residue filtration. This does not strengthen
coset equality to group/vector equality or postulate equality of metric data.
Actual discrepancy>theta implies the IH accuracy theta/2. Actual character
integrality, true affine source, all-real factor/error and complete child tables
then apply the registered ORIGINAL coefficient transport. Invalid/empty pools
carry conditional defaults only, never a false good character or inverse.

3. Fourier assembly. Actual nonzero terminal frequencies close to original
inverse conclusion under only actual degree-reduced IH and strictly smaller
same-degree IH. The SAME original finite terminal-frequency set from the true
zero/nonzero decomposition is used. Finite budgets/thresholds and a genuine
ceil(4/eta^2) bound give ONE threshold before all raw sources. The zero mode
uses the true terminal quotient's lower-degree inverse. No frequency is dropped;
unit-cube/univariate-interval means are related by the registered exact identity.

4. NEW complete small-N proof. A nonempty actual finite sample set has a maximum
point discrepancy. Convex norm bound proves that this sample is at least the
original mean discrepancy. Its actual logarithmic value constructs a constant
vector polynomial, with TRUE weights because L.layer 0=top. Its orbit is the
actual anchored native point at every integer input. Every positive resample
has exactly the same discrepancy against the SAME original unit observable and
canonical Haar mean. Therefore the already proved large-N step at its fixed
positive threshold yields an actual nonzero original horizontal character with
the SAME fixed norm budget. The character may depend on the original source;
its norm/grid budget does not. This is not a circular invocation of the full
inverse: it calls only the independently proved large-N induction STEP.

The original scalar projection has true degree<=ell from original source
weights and terminal layer=bottom, even if raw zero vector terms have higher
ordinary degrees. For N below the fixed threshold, circle norm<=1 and actual
degree give ALL positive monomial rows at most threshold^ell. Above-degree
rows vanish. Integer Stirling transfer proves ALL binomial rows. The final
natural budget is fixed before raw p/N/observable. Trivial quotient data cause
no exception: a positive discrepancy anchor cannot exist there, so no horizontal
character existence axiom or nontriviality assumption has been inserted.

5. Genuine unconditional induction. NativeRationalUnitInverse first strong-
induces on degree over ALL actual step bounds/data/filtrations. Degree zero/one
are registered genuine bases. At degree>=2 it strong-induces on the ACTUAL
natural sum of finranks of layers 2..ell, over ALL native data at the same step
bound. Both true lower-degree child types have index ell-1, and their full
inverse is obtained from the actual degree IH. Every canonical residue child
has strictly smaller natural nonlinearity, giving the precise same-degree IH.
No standalone inverse for a kernel, oracle record, supplied character or custom
axiom is used. Nonlinearity zero is handled by this legitimate strong induction;
a supposed smaller child would have an impossible negative natural rank sum.

6. Exact theorem scope. The final public Lean theorem is
Hindman168.native_rational_weighted_inverse_unit :
  NativeRationalWeightedInverseStatement D L Unit
for every legitimate actual native datum D and finite rational Lie filtration L.
The definition includes every delta>0, ONE positive natural budget before all
raw sources, every original N>0, every unit-Lipschitz observable, a NONZERO
original horizontal lattice character, original norm/grid, and BOTH COMPLETE
raw original monomial/binomial tables on all positive Unit multiindices.
There are no lower-degree/same-degree inverse hypotheses in this theorem.

7. Remaining full goal. This is the single-variable fixed-data existential
quantitative inverse. It does not assert the corrected multiparameter theorem
or explicit source delta-power laws. Native line-source construction, common
finite original character/dense-direction/basepoint coefficient reconstruction,
separate interval Gowers correlation inverse, rough progression comparison,
cube/Alignment and final FS/FP theorem remain open. The older source slab issue
concerns a repaired intermediate estimate and is not a terminal obstruction.
All six pinned OpenAI source sections and exact rational slab arithmetic are
rechecked. Public repository/PR/prize user milestone has not been reached.
''', encoding='utf-8')
print(PREFIX)
