from pathlib import Path
import json,re
prefix='round-native-rational-terminal-fourier-zero'
old='round-native-rational-degree-one-inverse'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==20,modules
components=[
 'ANY original finite rational Lie filtration now has an ACTUAL terminal-layer torus/action on SAME original native cosets. Torus rank is rank of ORIGINAL F(ell), original terminal rationality/centrality/lattice inputs are PROVED, actual group torus projection/eigenaction uses SAME integrated F(ell), and original specified-metric continuity/canonical Haar probability/integral invariance are discharged.',
 'Actual original terminal orbital unit-observable family is compact in uniform function norm. Actual continuous Fourier projections satisfy genuine torus/GROUP eigencharacter laws, norm contraction, zero invariance, projection composition/idempotence and NONZERO-frequency ORIGINAL canonical Haar mean zero. Function-space Lipschitz/compact families are PROVED; no unsupported SPATIAL Lipschitz estimate is assumed.',
 'One FIXED finite original terminal Fourier kernel reconstructs ALL original unit observables uniformly. Fixed finite actual frequencies and a positive threshold detect EVERY original finite-sample canonical discrepancy. Actual original frequency l1 budget is fixed before ALL observations/samples. GENUINE bounded alternative retains ZERO-mode discrepancy OR NONZERO original terminal frequency finite mean; zero mode is never discarded.',
 'ACTUAL original terminal native image-lattice factor is surjective, equivariant, and has fibers EXACTLY original terminal subgroup action orbits. It is an OPEN QUOTIENT under BOTH actual specified native source/target metrics, from PROVED metric/natural quotient topology identities. Original lattice need not be normal; no replacement coordinate lattice or metric is used.',
 'ACTUAL zero Fourier mode descends continuously to SAME actual terminal native quotient/image lattice, preserving EVERY original point value and uniform norm contraction. Original pushforward probability is PROVED a probability/invariant under the ACTUAL quotient group and equals ACTUAL quotient native canonical Haar by genuine uniqueness. Native metric/Borel transports are explicitly proved, not treated as assumed identical measures.',
 'Genuine original action invariance/Fubini proves ZERO projection preserves ORIGINAL Haar mean. Descended zero-mode integral against ACTUAL quotient canonical Haar equals SAME original projection/original Haar integral. Original zero-mode finite discrepancy equals ACTUAL quotient canonical discrepancy on SAME projected original samples and SAME specified metric.',
 'Actual zero-mode descended family is compact in FUNCTION-space uniform norm. A fixed finite bounded SPATIAL Lipschitz approximation family in ACTUAL quotient metric is CONSTRUCTED, then normalized to a fixed finite TRUE UNIT quotient observable family. Fixed positive detection threshold and family precede ALL original observations and finite samples; contraction of projections is never misused as spatial Lipschitz continuity.',
 'Zero-mode unit detection is APPLIED to ACTUAL original logarithmic-polynomial orbits, using exact original native factor/native Exp/coefficient projection sample identities. For TRUE weighted original sources, ACTUAL projected/zero-trim polynomial has SAME genuine image-filtration weights and ordinary degree ell-1, while a TRUE UNIT fixed quotient observation detects its ACTUAL quotient canonical Haar discrepancy. COMPLETE scalar pullback polynomial and ALL original scalar coefficients survive. Original coefficients remain UNBOUNDED and actual image filtration is never re-stretched.'
]
remaining=base['last_round']['remaining']
needle='NEXT: genuine arbitrary rational-filtration terminal torus/nonzero Fourier branches, HIGHER-DEGREE recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport beyond proved degree-zero and degree-one base cases;'
assert needle in remaining
replacement='NOW ANY original finite rational Lie filtration has ACTUAL ORIGINAL terminal torus/action/canonical-Haar invariance, continuous Fourier projections/GROUP eigenlaws/NONZERO frequency mean zero, fixed finite uniform reconstruction/frequency selection/l1 bound, and genuine ZERO-mode OR NONZERO original-terminal-frequency alternative. ACTUAL terminal image-lattice native factor is surjective/equivariant with exact fibers and open quotient in BOTH specified metrics. ZERO mode descends to ACTUAL native terminal quotient; original pushforward equals TRUE quotient canonical Haar by PROVED probability/invariance/uniqueness and explicit metric/Borel transport. Original/descended ZERO integrals and canonical discrepancies agree on EXACT original samples. Compact FUNCTION-space zero family yields fixed finite actual SPATIAL Lipschitz/unit child family and positive detection threshold before ALL source inputs. Actual ZERO-mode weighted-polynomial reduction produces SAME actual image weights, ordinary degree ell-1, complete original scalar pullback and large TRUE quotient native canonical discrepancy in a fixed UNIT child observation. NEXT: actual NONZERO-frequency relative-pair observables/factor/quotient canonical Haar/finite-unit detection and original normalization samples for ANY original rational filtration; ORIGINAL horizontal-character pullback for zero quotient and genuine NONZERO relative character reconstruction under HIGHER-DEGREE quantitative induction beyond proved degree-zero/one bases;'
remaining=remaining.replace(needle,replacement)
x=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
 x=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),x,flags=re.M)
x=x.replace('Audit genuine ORIGINAL rational degree-one NONZERO inverse, exact abelian-data/canonical-Haar compatibility, raw weighted coefficients, complete finite variable equivalence and actual recursive degree-one state application.','Audit actual arbitrary original rational terminal Fourier action/selection and TRUE zero-mode native quotient canonical-Haar/metric/unit/weighted-polynomial degree reduction.')
x=re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions and Green-Tao section 7: actual ANY rational terminal Fourier bounded alternative and zero-mode canonical-Haar/metric/finite-unit/weighted-polynomial reduction proved; nonzero relative character induction/full prize target open'", x)
Path(prefix+'-audit.py').write_text(x,encoding='utf-8')
review='''JSP-000168: actual arbitrary original terminal Fourier and zero-mode reduction
Author mathematical review, 2026-10-13. Not independent kernel replay or external peer review.

Route: retained six OpenAI sections at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
especially 06_rough_progressions; Green--Tao section 7, Proposition 7.2:
https://arxiv.org/html/0709.3562v4 . Corrected equal-side scope:
https://arxiv.org/html/1311.6170v3 . Original coefficients remain UNBOUNDED.

1. The actual terminal layer is ORIGINAL F(ell), with original rationality
   against SAME original Gamma and genuine centrality from F.bracket and
   F(ell+1)=0. Actual integrated group terminal equals true Exp subgroup.
   Backend lattice/torus construction uses SAME original central subspace
   and lattice intersection. Torus rank is its actual real rank; no lower-
   central re-stretch or substitute coordinate lattice is introduced.
2. Actual original torus/group action on original specified-metric cosets
   is continuous, additive and commutes with original group translations.
   Probability/integral invariance are proved for actual ORIGINAL canonical
   Haar. Actual original terminal group projection realizes this action.
3. Genuine continuous Fourier projections have actual torus/GROUP eigenlaws,
   composition/idempotence, zero-mode invariance and NONZERO-frequency
   ORIGINAL Haar mean zero. Zero-frequency is ALLOWED in finite selection.
   Nonzero terminal frequency is a VERTICAL frequency on the actual terminal
   torus, NOT an already-reconstructed original horizontal character.
4. Original unit orbital family is compact in uniform function norm. A
   single finite Fourier kernel reconstructs EVERY original unit observable
   uniformly. Fixed support/positive threshold and actual frequency l1
   budget precede ALL original observations/samples. The bounded alternative
   is ZERO-mode discrepancy OR a NONZERO-frequency original finite mean.
   It is false to discard zero mode, and this proof explicitly retains it.
5. Actual terminal native image-lattice factor has true surjectivity,
   equivariance and EXACT original terminal subgroup fibers. Both native
   specified-metric/natural quotient topology equalities are used to PROVE
   open quotient on source AND target. Original Gamma may be nonnormal;
   normality/centrality belong only to actual terminal subgroup.
6. True zero-mode group invariance descends continuously through these
   actual fibers into the ACTUAL native terminal quotient/image lattice.
   Every original point value is retained. Uniform norm is contracted;
   this is a function-space norm statement, not spatial Lipschitz regularity.
7. Actual original pushforward probability is constructed and its true
   probability/full quotient-group invariance are proved. Native canonical
   probability uniqueness identifies it with TRUE quotient native Haar.
   Metric/natural Borel sigma-algebra compatibility is explicitly proved.
   No presumed replacement Haar measure, disintegration or density is used.
8. Original actual action invariance/Fubini proves zero-mode averaging
   preserves original Haar mean. Pushforward/canonical/Borel integrals agree
   for the actual descended observable; its child canonical integral equals
   SAME parent zero/original integral. EXACT original zero-mode discrepancy
   equals actual terminal quotient canonical discrepancy at SAME projected
   original samples, with SAME original specified metrics.
9. Actual zero-mode FAMILY is compact in uniform function norm. This does
   NOT imply its members are spatial unit Lipschitz. A proved compact-family
   approximation theorem produces one finite bounded spatial Lipschitz
   family in ACTUAL child metric. Real positive bounds are normalized to
   a finite TRUE UNIT child family, with positive detection threshold fixed
   BEFORE ALL source observations/samples. This repairs the analytic input
   needed to feed a genuine child inverse, rather than assuming regularity.
10. Detection is applied to ACTUAL logarithmic-polynomial source orbits.
    Exact native factor/Exp/coefficient projection identity retains ALL
    original integer samples. For TRUE weighted sources the actual image
    weights are PROVED in SAME original projected filtration; zero trimming
    gives actual degree <=ell-1 while retaining full scalar pullback and
    EVERY original scalar coefficient. Source representations can have
    arbitrary high-degree zero-vector terms. No bound on original vector
    coefficients/lattice logs, or re-stretched image filtration, is assumed.
11. Degenerate actual terminal rank zero and ell=0 are allowed. Nonzero
    frequency premise is then impossible; the genuine zero alternative
    remains available. No unjustified nontrivial-terminal hypothesis or
    empty-sample claim is introduced. The proved terminal discrepancy base
    still requires nonempty samples; these selection/detection identities
    correctly allow arbitrary finite samples.

Review boundary: actual NONZERO-frequency relative-pair observable descent,
actual reduced native canonical Haar/metric/unit detection for ANY rational
filtration, and original normalization samples in that Fourier branch still
need construction. Horizontal-character pullback in zero branch and genuine
ORIGINAL NONZERO relative character reconstruction with fixed operator/grid/
binomial bounds under HIGHER-DEGREE inverse induction remain open. Current
zero-mode result is a TRUE inverse REDUCTION, not the complete higher-degree
inverse. Corrected full multivariate inverse, separate interval Gowers
correlation inverse, progression descent, conditional cube laws/posterior/
positive Alignment and final FS/FP extraction remain open. StrongConjecture
UNPROVED; no unavoidable obstruction established. Publication/application
milestone not yet reached.

Exact remaining record:
'''+remaining+'\n'
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
ds=[(k,n) for m in modules for k,n in re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)',Path(m).read_text(encoding='utf-8'),re.M)]
print(json.dumps({'modules':len(modules),'theorems':sum(k in {'theorem','lemma'} for k,n in ds),'definitions':sum(k in {'def','abbrev'} for k,n in ds)}))
