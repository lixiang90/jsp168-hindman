from pathlib import Path
import json
import re

prefix = 'round-central-subspace-quotient'
old = 'round-ordered-central-flag'
modules = ['Hindman168/'+m+'.lean' for m in [
    'NativeCentralSubspaceSubgroup', 'NativeCentralSubspaceCosetRelation',
    'NativeCentralSubspaceQuotientHomeomorph', 'NativeCentralSubspaceQuotientCharted',
    'NativeCentralSubspaceQuotientSmoothProjection', 'NativeCentralSubspaceQuotientSmoothLift',
    'NativeCentralSubspaceQuotientLieGroup', 'NativeCentralSubspaceQuotientDifferential',
    'NativeCentralSubspaceQuotientTangent', 'NativeCentralSubspaceQuotientNativeExponential',
    'NativeCentralSubspaceQuotientNativeLogarithm', 'NativeCentralSubspaceLieIdeal',
    'NativeCentralSubspaceQuotientLattice', 'NativeCentralLayerKernel',
    'NativeCentralSubspaceLowerCentralImage', 'NativeCentralSubspaceLayerLatticeLift',
    'FiniteRealQuotientDimension', 'NativeTerminalCentralSubspace', 'NativeTerminalCentralQuotient']]
components = [
    'Every specified original central real subspace has an actual exponential subgroup proved normal and closed. Actual exponential coset equivalence constructs a homeomorphism between the original vector-space quotient and the original group quotient with its retained quotient topology.',
    'The actual central-subspace quotient has a constructed smooth chart, smooth projection and right lift, genuine smooth original quotient multiplication/inversion and Lie group structure. Its actual identity differential is the actual real quotient projection, with its actual specified kernel.',
    'Actual original and actual quotient native exponentials and logarithms commute with the actual projections. The quotient coordinate exponential/logarithm are identified with the actual native maps; contractibility and simple connectedness are proved.',
    'The specified central subspace is an actual native Lie ideal. When rational for the actual original lattice, its actual quotient lattice image is proved discrete; original lattice cocompactness gives quotient-image cocompactness.',
    'Actual original group and Lie lower-central layers have exactly the actual quotient lower-central images. If the specified central subspace lies in a layer, the actual quotient kernel lies in that original group layer, giving exact relative original lattice-layer images and actual exponential lattice-layer lifts. Closedness is discharged from finite dimension in the Lie image/lift applications.',
    'A nontrivial original model has a last nonzero actual lower-central layer. This layer is a rational central subspace contained in every earlier layer and has a strictly smaller actual quotient dimension.',
    'For an actual original discrete cocompact lattice and nontrivial model, an actual terminal central quotient is constructed with discrete cocompact quotient lattice, strictly reduced dimension, and exact original lattice-layer images for every prior layer. This supplies compatible quotient inputs; full adapted ordered basis induction remains open.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
gap = 'The actual full-center lift condition is not discharged for arbitrary original lower-central layers. Use a compatible rational central ideal or prove the actual relative lattice-image condition before claiming full adaptation.'
assert remaining.count(gap) == 1
remaining = remaining.replace(gap,
    'The actual full-center lift condition is not discharged for arbitrary original lower-central layers. A new actual central-subspace quotient construction now proves the retained quotient topology, smooth Lie operations, native exponential/logarithm projection, rational quotient lattice discreteness/cocompactness and exact original lower-central images. Kernel containment is discharged whenever the specified central subspace lies in the layer. A last nonzero original lower-central layer is proved rational and central, contained in every earlier layer, and strictly reduces actual quotient dimension. An actual terminal central quotient therefore has exact prior relative lattice-layer images and a discrete cocompact quotient lattice. Complete the actual ordered lattice basis extension and full filtration-adapted smooth dimension induction using these compatible quotients; that induction is still unproved.')
review = [
    'The subgroup is the actual image of the original native exponential restricted to the specified subspace. Original central exponential addition and negation prove subgroup closure. Membership is exactly original logarithm membership, proving actual closedness from finite-dimensional subspace closedness. Its actual inclusion in the original group center proves normality; no normal subgroup is supplied as a premise.',
    'The coset relation is the actual quotient relation for this subgroup: v-w in V iff exp(v)^-1*exp(w) in N. The reverse direction uses the actual central logarithm of that product, original exponential multiplication and actual injectivity. Homeomorph.Quotient.congr uses the original exponential homeomorphism and the proved actual relation; original quotient topology is retained.',
    'A single chart is induced by the actual quotient homeomorphism. Projection smoothness follows from original global logarithm and the actual continuous linear quotient projection. The right lift uses an actual finite real quotient linear section, actual original exponential, and actual quotient logarithmic coordinates. Genuine quotient multiplication and inversion are proved smooth through this lift and the original operations. Every local quotient T2/chart/Lie instance is applied to the specified V and hV explicitly.',
    'The projection/lift right inverse proves differential surjectivity. The actual tangent calculation identifies the projection identity differential with the actual finite real quotient projection. The original smooth-homomorphism native exponential theorem then proves original/quotient exponential compatibility; actual quotient global inverse proves logarithm compatibility and coordinate/native map equality. Quotient nilpotency is inherited from the original group, and simple connectedness is established by actual contractibility, not an existence premise.',
    'The actual central native Lie ideal has precisely V as its real model and precisely the actual exponential subgroup as its group. Rational compact representatives give g=x*gamma with x in the actual subgroup. Since g and x lie there, gamma lies there too; this explicitly establishes the Gamma-intersection representative required by the actual normal quotient discreteness theorem. Quotient cocompactness uses the actual surjective quotient map.',
    'The group lower-central image equality follows from the actual surjective quotient homomorphism and the actual lower-central image theorem. The Lie-layer equality uses exact original and quotient group/Lie lower-central equality and actual exponential projection/injectivity in both directions. The Lie equality and lift theorem construct IsClosed(V) from finite dimension within their statements and proofs; no new closedness assumption remains in these applications.',
    'Relative lattice-layer lifting explicitly rewrites the actual quotient homomorphism kernel to N and proves N lies in the actual original group layer by the exact original Lie/group layer equality. The previously reviewed kernel-contained intersection image theorem then applies. Actual original exponential representatives and actual quotient native exponential injectivity produce a vector in the original Lie layer whose exponential is in original Gamma and whose actual projection is the requested quotient vector.',
    'Nat.find selects the first actual zero lower-central layer, which is positive because the zero-index layer is top and the original model is nontrivial. The preceding layer is therefore actually nonzero with zero next layer. Its native bracket is zero by next-layer membership and alternating symmetry, so it lies in the actual center. Original lattice rationality of actual lower-central layers and actual antitonicity establish rationality and containment in every prior layer. Actual quotient rank-nullity and positive subspace dimension prove strict dimension decrease.',
    'The terminal quotient existence theorem packages the actual terminal layer, its proved central inclusion, actual discrete cocompact quotient lattice, strict model dimension decrease and exact original lattice-layer images for every prior layer. The model nontriviality is explicit; the zero-dimensional induction case is not claimed here. Full ordered basis construction, smooth ordered inverse, consecutive blocks in the whole group, and the paper horizontal coefficient norm still require actual induction and extension proofs.',
    'This is author-side proof and hypothesis review. The complete original prize theorem, analytic quantitative Leibman existence/modular bounds, independent kernel replay, external review, public repository, PR and award application remain unproved/unperformed. All retained registered proof sources and selected axiom sets must remain unchanged.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions actual compatible rational terminal central quotient and relative lattice lifts; full adapted smooth ordered basis induction and quantitative existence open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual central-subspace quotient audit for', len(modules), 'modules.')
