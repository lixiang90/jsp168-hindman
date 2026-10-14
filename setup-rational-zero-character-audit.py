from pathlib import Path
import json,re
prefix='round-native-rational-zero-character-induction'
old='round-native-rational-terminal-fourier-zero'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==11,modules
components=[
 'ACTUAL terminal quotient characters pull back through TRUE original model/group projections. Actual model surjectivity PROVES original nonzeroness; exact original native Log/group projection compatibility PROVES multiplication law and ORIGINAL commutator annihilation. Original lattice integrality follows from SAME actual image lattice membership. No original nonzero/horizontal/integrality premise is assumed.',
 'A FIXED ORIGINAL operator budget A*(1+norm(actual model projection)) bounds the actual original character and produces SAME ORIGINAL finite horizontal grid from actual child norm/horizontality. All original norm/grid constants precede source coefficients and sample lengths; no norm/size compatibility input or assumed parent character is introduced.',
 'COMPLETE original scalar polynomial and EVERY original monomial coefficient equal those of actual projected/zero-trim polynomial under actual character pullback. TRUE scalar degree is at most ell-1 from SAME genuine image weights. Actual binomial box enlargement above true degree is PROVED invariant, so child ell-1 binomial table equals ORIGINAL parent ell table. Merely retaining monomial coefficients would not justify this degree-bound change; it is now discharged.',
 'The FULL desired NativeRationalWeightedInverseStatement is explicitly named as a PROPOSITION, NOT an axiom, instance, certificate or assumed data field. Its desired quantifiers cover ANY finite variable type, all raw weighted coefficients, positive equal-cube lengths, original unit observations and original ACTUALLY NONZERO horizontal character/finite grid/operator/monomial/binomial bounds. Genuine degree-ZERO and degree-ONE bases are PROVED; higher-degree universal statement remains UNPROVED.',
 'GENUINE arbitrary-degree ZERO-MODE inverse induction reduction is now PROVED. Its sole inverse premise is the FULL desired LOWER-DEGREE conclusion on ACTUAL original terminal quotient data/true image filtration. All original zero-mode detection/canonical Haar/metric/unit/weights/degree inputs are proved, and ORIGINAL nonzero character/integrality/horizontality/operator/grid/BOTH raw coefficient conclusions follow by actual pullback. This is a CONDITIONAL mathematical induction step, not an achieved higher-degree inverse.',
 'Actual zero induction reduction has a FIXED NATURAL original norm/coefficient budget and ORIGINAL finite grid, derived by rounding the true operator budget. Combining it with actual bounded original Fourier selection gives ORIGINAL horizontal obstruction OR bounded ACTUAL NONZERO terminal-frequency finite mean. Shared bounds/frequency family precede ALL original source polynomials, positive sample lengths and unit observations.',
 'The COMPLETE degree-TWO ZERO-FREQUENCY branch is PROVED with NO child inverse hypothesis: actual child has true filtration degree ONE, whose FULL inverse is already proved. The actual ORIGINAL nonzero character/true finite grid/operator bound/BOTH original parent degree-two monomial/binomial bounds are produced for ANY finite variable type and UNBOUNDED raw weighted coefficients.',
 'Degree-TWO original full-discrepancy bounded alternative is PROVED with child hypothesis fully discharged: ORIGINAL nonzero horizontal obstruction with all required bounds OR bounded original NONZERO terminal-frequency signal. The second branch remains unresolved, so this is NOT the full degree-two inverse or the prize theorem. All earlier actual rational geometry/recursion/canonical measure/degree-zero-one/Fourier/zero-unit results are retained.'
]
remaining=base['last_round']['remaining']
needle='ORIGINAL horizontal-character pullback for zero quotient and genuine NONZERO relative character reconstruction under HIGHER-DEGREE quantitative induction beyond proved degree-zero/one bases;'
assert needle in remaining
replacement='NOW ACTUAL arbitrary terminal quotient character pullback PROVES ORIGINAL nonzero/horizontal/lattice-integral character, true fixed operator budget and ORIGINAL finite grid. COMPLETE original scalar/monomial coefficients and true scalar degree ell-1 survive, and actual binomial degree extension PROVES child ell-1 table equals ORIGINAL parent ell table. FULL desired NativeRationalWeightedInverseStatement is named ONLY as a proposition; degrees zero/one are PROVED, higher universal inverse UNPROVED. Genuine arbitrary-degree ZERO-MODE induction step is PROVED CONDITIONALLY on FULL LOWER-DEGREE child inverse, with ALL actual original geometry/measure/unit/weights and character/grid/operator/BOTH coefficient inputs discharged. Fixed NATURAL budget and actual bounded Fourier alternative combine the zero character result with the remaining nonzero-mode signal. Degree-TWO ZERO-MODE inverse is NOW FULLY PROVED with NO child inverse hypothesis; degree-TWO original full-discrepancy horizontal-character OR bounded nonzero-frequency alternative is PROVED. Neither the unresolved degree-two nonzero branch nor higher-degree universal inverse is declared solved. NEXT: genuine NONZERO relative character reconstruction/ORIGINAL character pullback under HIGHER-DEGREE quantitative induction beyond proved degree-zero/one and closed degree-two-zero bases;'
remaining=remaining.replace(needle,replacement)
x=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
 x=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),x,flags=re.M)
x=x.replace('Audit actual arbitrary original rational terminal Fourier action/selection and TRUE zero-mode native quotient canonical-Haar/metric/unit/weighted-polynomial degree reduction.','Audit ACTUAL original nonzero terminal character pullback, complete raw scalar/binomial degree transport, genuine conditional zero-mode induction, closed degree-two zero branch and bounded nonzero-mode alternative.')
x=re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions and Green-Tao section 7: actual ORIGINAL zero character pullback and true conditional zero induction; degree-two zero inverse/alternative proved, nonzero relative reconstruction/full prize theorem open'", x)
Path(prefix+'-audit.py').write_text(x,encoding='utf-8')
review='''JSP-000168: actual original zero character reconstruction and induction step
Author mathematical review, 2026-10-13. Not independent kernel replay or external peer review.

Route: retained six OpenAI sections at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
06_rough_progressions and Green--Tao section 7, Proposition 7.2:
https://arxiv.org/html/0709.3562v4 . Corrected equal-side scope:
https://arxiv.org/html/1311.6170v3 . Original coefficients remain UNBOUNDED.

1. Child character is composed with TRUE original terminal model projection.
   PROVED original model surjectivity prevents a nonzero child functional
   becoming zero on the original model. Actual original Log compatibility
   identifies the pulled real group character with actual child group
   character composed with TRUE original group projection.
2. Actual group projection is a group hom. Child horizontality yields real
   multiplicativity; genuine continuous-character linearization proves the
   ORIGINAL lower-central commutator model is killed. Every ORIGINAL gamma
   maps into SAME ACTUAL child image lattice, and exact Log compatibility
   proves original lattice integrality. Original horizontal/nonzero/integer
   character conclusion is DERIVED, not assumed.
3. True continuous-linear operator composition bounds the original norm.
   Fixed budget A*(1+norm(P)) is >=A and bounds actual composition norm.
   Existing proved native finite-grid theorem supplies the ORIGINAL grid
   from this derived norm and original integrality/horizontality. There is
   no parent size/character compatibility premise. Quotient is not assumed
   isometric in its arbitrary specified coset metric.
4. COMPLETE actual original scalar polynomial equals child projected AND
   zero-trim scalar polynomial; hence EVERY monomial coefficient agrees.
   True weighted image terminal vanishing gives scalar degree <=ell-1.
   Original representations may have high-degree zero-vector terms; their
   raw coefficients and unbounded nonzero vector values are not substituted.
5. Actual binomial coefficient sums use a bounding box, so different child
   and parent degree parameters cannot simply be identified by scalar
   equality. Box monotonicity and TRUE polynomial degree force all extra
   monomial coefficients to zero. This PROVES degree extension invariance,
   and child ell-1 binomial table equals ORIGINAL parent ell table. This
   resolves the real coefficient-transport gap rather than hiding it in
   an assumed binomial interface or keeping the wrong child parameter.
6. NativeRationalWeightedInverseStatement is a named FULL desired proposition,
   NOT an axiom, class instance, data field or universal proved result.
   It requires actual ORIGINAL NONZERO horizontal character, fixed finite
   grid/operator bound and BOTH ORIGINAL coefficient tables, with bounds
   preceding all source p,N,H. Only degree-zero and degree-one bases are
   PROVED. Degree-zero uses the nonempty positive cube and actual terminal
   canonical Haar discrepancy zero, not an invalid empty-average claim.
7. General zero-mode induction theorem is CONDITIONAL precisely on this
   FULL lower-degree conclusion on ACTUAL native terminal quotient/actual
   IMAGE filtration. It assumes no parent character, parent bounds,
   geometry, canonical measure identity, degree drop or unit detection.
   Those are all supplied by actual proved original constructions. A
   native unit child witness and actual weighted degree-reduced coefficient
   polynomial feed the child premise; actual pullback reconstructs original
   nonzero/horizontal/integer character and BOTH coefficient bounds.
   This is a genuine induction step; it DOES NOT prove the higher inverse
   merely because its child premise is named in a proposition.
8. Rounding true operator budget gives a positive fixed NATURAL budget.
   Actual original finite grid is obtained from that larger true norm
   bound; original monomial/binomial bounds enlarge consistently. Existing
   actual Fourier selection then combines zero reconstruction and bounded
   NONZERO vertical frequency signal into one fixed-budget alternative.
   Nonzero vertical mode is NOT a reconstructed horizontal character.
9. For parent filtration degree TWO, actual terminal child has degree ONE.
   Its desired inverse is ALREADY PROVED on SAME actual group/metric/Haar
   and ANY finite variable type. The child hypothesis is fully discharged,
   proving COMPLETE actual degree-two ZERO-frequency inverse with ORIGINAL
   nonzero character/grid/operator/parent degree-two monomial/binomial
   bounds. No original coefficient/lattice-log bound or assumed inverse
   certificate is introduced.
10. Degree-two full-discrepancy alternative likewise has NO inverse premise:
    actual original horizontal obstruction OR bounded actual nonzero
    terminal-frequency signal. The latter remains unresolved. This is NOT
    a complete degree-two inverse, arbitrary-degree inverse or prize theorem.

Review boundary: generic actual NONZERO-frequency relative-pair observable
descent/canonical Haar/metric/unit detection and ORIGINAL nonzero relative
horizontal-character reconstruction remain open, including the second
degree-two alternative. General zero induction still needs its true child
inverse from a complete degree induction; no higher universal statement is
claimed. Corrected full multivariate inverse, separate interval Gowers
correlation inverse, rough progression descent, conditional cube laws/
posterior/positive Alignment and final FS/FP extraction remain open.
StrongConjecture UNPROVED; no unavoidable obstruction established.
Publication/application milestone not met.

Exact remaining record:
'''+remaining+'\n'
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
ds=[(k,n) for m in modules for k,n in re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)',Path(m).read_text(encoding='utf-8'),re.M)]
print(json.dumps({'modules':len(modules),'theorems':sum(k in {'theorem','lemma'} for k,n in ds),'definitions':sum(k in {'def','abbrev'} for k,n in ds)}))
