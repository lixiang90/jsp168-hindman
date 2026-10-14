from pathlib import Path
import json,re
prefix='round-rough-horizontal-coordinate-budget'
old='round-rough-character-grid-uniform-degree'
modules=['Hindman168/'+m+'.lean' for m in [
'RoughBasisFunctionalNorm','RationalSubspaceArbitraryBasis','RationalSubspaceSplitBasis',
'RoughNativeCommutatorBasis','RoughNativeBasisCharacterGrid','RoughNativeCommutatorCharacterGrid',
'RoughNativeRealBoxBasisTransfer','RoughHorizontalIntegerSize','RoughNativeRealBoxCoordinateTransfer']]
components=[
'A fixed explicit positive basis norm budget converts bounds on all actual basis evaluations to an operator norm bound, including the zero-dimensional case. A horizontal functional vanishes on basis vectors in its actual commutator kernel, so only horizontal evaluations need bounds.',
'The genuine Euclidean norm of the integer horizontal coefficient vector is defined and its square is exactly the finite sum of coefficient squares. This yields individual basis value bounds and the fixed operator norm budget under explicit coordinate identification.',
'Every rational basis of the original full rational form lifts through the proved natural scalar extension to a real basis with precisely the same actual columns.',
'A rational subspace and a chosen rational complement give a genuine split real basis. For a rational real subspace the first block is contained in and spans precisely that original real subspace.',
'The actual original commutator layer has a fixed rational complement and an actual real split basis whose first block spans exactly the original commutator layer and whose entire basis lies in the original rational log span.',
'Bounds on horizontal complement basis values, or identified bounded integer horizontal coordinates, place original nonzero lattice-integral horizontal functionals in the actual fixed finite horizontal grid. Original lattice integrality remains explicit.',
'The corrected actual half-open real-box coefficient transfer accepts a fixed basis value budget or a genuine Euclidean integer horizontal coordinate size budget. It constructs the actual finite candidate grid with all constants before varying source data, while retaining equal-cube quantitative existence as an explicit premise.'
]
remaining=json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
remaining=remaining.replace('Prove the actual equal-side quantitative Leibman input and adapted rational basis; in particular prove character existence and the uniform size bound and connect the paper Malcev-coordinate size to the fixed functional norm budget.',
'The actual rational real basis adapted to the commutator layer and the conversion from identified Euclidean horizontal integer coordinates to the fixed functional norm budget are now proved. This split basis is not yet a lattice-coordinate Malcev basis adapted to the whole filtration; integrality of its complement coordinates is not asserted. Prove the actual equal-side quantitative Leibman input, including character existence and uniform coefficient bounds, and construct and identify the required full lattice-coordinate Malcev basis.')
review=[
'The explicit norm budget is the maximum of the actual fixed basis coordinate-map norm times the basis cardinality and one. It is positive even for empty bases and independent of every varying character, polynomial and scale.',
'The horizontal square-size argument uses only nonnegative squares and actual kernel membership outside the specified horizontal index set. The integer coordinate evaluation identity is an explicit hypothesis, not inferred from rationality.',
'The coefficient size is an actual EuclideanSpace norm on the finite horizontal subtype. Its squared norm is exactly the finite coefficient-square sum; no maximum norm is silently substituted for the paper size.',
'The arbitrary rational basis is lifted by base change and the already proved natural scalar extension equivalence. Equality of actual columns is proved for every index.',
'The rational complement is fixed by vector space complementation in the actual rational log span. Both split blocks are finite bases; real spanning of the first block uses the actual rationality of the original commutator layer.',
'The constructed split real basis is adapted only to the original commutator layer. It is not claimed to give lattice second-kind coordinates, horizontal integer coefficients for every integral character, or adaptation to all filtration layers.',
'The real-box transfer preserves all allowed real endpoints and uses the corrected equal-cube analytic premise. Character existence, exact binomial equality and modular coefficient bounds remain explicit inputs. Norm conversion and a finite grid do not prove quantitative equidistribution.',
'All new proofs are checked with autoImplicit=false, followed by a full build, exact new declaration axiom reports, retained source hashes and retained axiom-set equality, and comparison of all six pinned primary sections. This is author-side verification only.'
]
src=Path(old+'-audit.py').read_text(encoding='utf-8')
src=re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix),src,count=1,flags=re.M)
src=re.sub(r'^OLD = .*$', 'OLD = '+repr(old),src,count=1,flags=re.M)
a=src.index('MODULES = ');b=src.index('\ndef declarations():',a)
src=src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a=src.index('        application_review=COMPONENTS+');b=src.index('\n        verified=summary',a)
src=src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src=re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions horizontal integer coordinate size, fixed functional norm budgets and actual rational commutator split basis; quantitative existence and full lattice Malcev basis remain open'",src)
Path(prefix+'-audit.py').write_text(src,encoding='utf-8')
print('Prepared audit engine for',len(modules),'new modules.')
