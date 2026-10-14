from pathlib import Path
import json,re
prefix='round-native-rational-weighted-relative'
old='round-native-rational-terminal-recursion'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==11,modules
components=[
 'ANY actual finite rational native Lie filtration now supports TRUE native weighted multiplication, product perturbations, affine shifts and both constant perturbations; actual real/integer filteredness follows from PROVED original native brackets/Exp layers. No original coefficient bound is assumed.',
 'For ANY actual weighted univariate source beginning at zero, the ACTUAL normalized integer pair lies in the ACTUAL relative native group. The ACTUAL first logarithmic coordinate polynomial and its weight-zero coefficients are constructed; its first-minus-second polynomial has weight ONE in SAME original F. Every aggregated coefficient difference is in F(totalDegree+1).',
 'The ACTUAL ambient pair polynomial equals the native product logarithm of EVERY original normalized integer pair. Native Log/inclusion compatibility and algebraic natural-grid coefficient recovery place ALL aggregate coefficients, including the constant, in SAME relative native model. Their SAME relative weights are PROVED, not assumed. True submodule polynomial retains evaluations, COMPLETE scalar polynomials and EVERY aggregate coefficient.',
 'The ACTUAL relative polynomial has real/integer filteredness in SAME actual internal relative group layers and exactly exponentiates to original normalized integer pair at EVERY integer. Zero-trim ordinary degree is at most ell even when original list contains arbitrarily high-degree zero-vector terms. No unsupported termwise ordinary-degree assumption is used.',
 'The ACTUAL weighted relative polynomial feeds SAME true terminal quotient and actual degree-reduced native data. All output weights are proved in ACTUAL projected IMAGE filtration, with zero-trim ordinary degree at most ell-1, exact original integer normalized pair group projection/coset factor samples and COMPLETE scalar pullback polynomial. No re-stretching is used.',
 'Both ACTUAL basepoint normalization and actual original linear lattice correction now preserve ANY true rational Lie weights, including successive original reduced IMAGE filtrations. Normalized logarithmic zero is PROVED from true native Exp/Log inverses; zero-trim ordinary degree is at most ell. Arbitrary constants and lattice logs remain unbounded.',
 'The FULL weighted RELATIVE-then-terminal polynomial construction is APPLIED to ACTUAL twice-normalized ORIGINAL ordinary-degree-bounded source: every weight and logarithmic-zero input is discharged at SAME stretch d. Exact original normalized integer-pair quotient samples and true output degree s*d-1 are proved; the stretch is never inflated to s*d.'
]
remaining=base['last_round']['remaining']
needle='NEXT: arbitrary WEIGHTED native normalized RELATIVE coefficient-polynomial reconstruction, especially feeding actual twice-normalized source, and exact original pair samples at successive true relative/quotient stages;'
assert needle in remaining
replacement='NOW arbitrary WEIGHTED normalized RELATIVE coefficient-polynomial reconstruction is CONSTRUCTED with actual integer pair samples, all aggregate coefficient membership, SAME relative weights, real/integer filteredness, COMPLETE scalar pullbacks and zero-trim degree ell. Actual relative-then-terminal polynomial reduction has degree ell-1 and is APPLIED to ACTUAL twice-normalized ORIGINAL source at SAME stretch d. Generic true basepoint/lattice-linear normalizations preserve ALL actual image filtration weights and PROVE normalized logarithmic zero and degree ell. NEXT: actual iterated weighted polynomial/orbit recursion using these normalizations and true relative/quotient stages;'
remaining=remaining.replace(needle,replacement)
x=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
 x=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),x,flags=re.M)
x=x.replace('relative weighted reconstruction/nonzero inverse/full prize theorem open','actual arbitrary weighted relative reconstruction and true quotient polynomial degree drop proved; recursive nonzero inverse/full prize theorem open')
Path(prefix+'-audit.py').write_text(x,encoding='utf-8')
review='''JSP-000168: arbitrary actual weighted relative polynomial reconstruction
Author mathematical review, 2026-10-13. Not independent kernel replay or external peer review.

Route: retained six OpenAI sections at adc7f1241b42e322a6451854ab7e4b4c146bf78a;
06_rough_progressions and Green--Tao section 7, Proposition 7.2:
https://arxiv.org/html/0709.3562v4 . Corrected equal-side scope:
https://arxiv.org/html/1311.6170v3 . All original coefficients remain unbounded.

1. Weighted product/perturbation proofs use actual native bilinear bracket
   and same F antitonicity. Both constants lie in F(0); constant perturbations
   lie in F(1)=top. The extra ONE weight is therefore justified for arbitrary
   unbounded constants. Real filteredness uses actual native Exp layer
   membership, integer filteredness uses genuine additive integer embedding.
2. Input logarithmic zero gives actual P(0)=1 by native Exp zero. The generic
   normalized-pair group lemma then gives membership in the original true
   relative group. No normality of the lattice is assumed.
3. The first logarithmic polynomial is an actual BCH product of translated
   p and true logarithms of t and P(1)^(-h). Integer exponential powers use
   true integer-scalar exponential identity, valid also for negative h.
   Association changes are justified by actual group associativity/Log.
4. First-minus-second logarithmic polynomial telescopes one translated
   difference and three constant product perturbations. Translation raises
   weight by ONE and each constant perturbation has the same ONE weight.
   Hence ALL aggregate coefficient differences lie in F(|J|+1); both
   coordinate coefficients lie in F(|J|). This is SAME original filtration.
5. Ambient product Log equals actual original integer pair. On natural grid
   values actual native relative Log/inclusion gives membership in the
   genuine relative tangent model. Algebraic quotient and scalar polynomial
   uniqueness recover ALL aggregate coefficients, including J=0. This
   avoids an unjustified assumption that every original list term belongs
   separately to the relative model.
6. Collection into actual subtype model preserves real evaluations,
   COMPLETE scalar polynomials, and EVERY aggregate coefficient. Monomial
   total degree plus proved coordinate/difference weights supplies true
   relative termwise weights. Real/integer filteredness is proved in true
   INTERNAL group layers using actual bracket and Exp/Log compatibility.
   Native Exp of the relative polynomial equals actual original pair for
   every integer, and therefore their nonnormal coset samples agree.
7. Source lists may contain high-degree scalar terms attached to zero
   vectors or canceling representations. No ordinary termwise degree of
   arbitrary source list is assumed. Removing zero terms from the collected
   actual relative polynomial gives degree <=ell using F_relative(ell+1)=0.
8. Actual relative polynomial projects through the proved actual terminal
   quotient. It retains projected weights, exact original integer pair
   group/coset factor samples, and COMPLETE scalar pullback polynomial.
   Output zero-trim degree <=ell-1 follows from actual image terminal
   vanishing, including ell=0. This is polynomial degree reduction, not
   only geometric construction and not an assumed inverse interface.
9. Both actual native normalizations preserve arbitrary true rational Lie
   weights. Actual linear correction uses F(1)=top, NOT a new lower-central
   stretch. Logarithmic zero follows from native Log(Exp(v))=v and Log(1)=0.
   These lemmas apply at later actual projected image filtration stages.
10. The construction is applied to actual twice-normalized ORIGINAL source
   with ordinary degree <=d. Every weight/zero input is PROVED and SAME
   original stretch d is retained. True output degree is s*d-1, with exact
   original normalized-pair quotient samples. No bound on coefficients,
   no replacement lattice and no inflated stretch s*d is assumed.

Review boundary: actual iterative polynomial/orbit recursion and analytical
discrepancy, canonical Haar/specified metric/unit/nonzero frequency transport
are still open. Geometry and polynomial degree reduction do not yet yield
an ORIGINAL nonzero horizontal character or quantitative inverse. Corrected
equal-side multivariate inverse, interval Gowers correlation inverse,
rough progression descent, cube laws/posterior/positive Alignment and final
FS/FP extraction remain open. StrongConjecture is UNPROVED. No unavoidable
obstruction is established. Public repository/PR/prize submission not yet
executed, consistent with requested publication milestone.

Exact remaining record:
'''+remaining+'\n'
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps({'modules':modules,'components':len(components)}))
