from pathlib import Path
import json
import re

prefix = 'round-leibman-short-lines'
old = 'round-filtered-horizontal'
modules = ['Hindman168/'+name+'.lean' for name in
    ['FiniteComplexDenseMean', 'LeibmanCubeLineAveraging', 'LeibmanCubeShortLines']]
components = [
    'Actual complex finite-set means commute in two variables, commute with subtraction of a constant on nonempty sets, and have a genuine difference norm bound. A mean of modulus at least 3*delta*B/4 with pointwise modulus at most B has at least delta/4 of its actual summands of modulus at least delta*B/2.',
    'For the actual integer cube [0,N)^kappa, any actual natural direction vector bounded by L, and actual short line length M>0, iterated original cube/line averaging changes the original complex cube mean by at most 2*B*card(kappa)*L*M/N. The genuine integer-box translation theorem controls every actual line shift before averaging.',
    'With actual line length floor(N/L^2), L>0, N>=L^2 and 8*card(kappa)<=delta*L, an actual original cube mean of modulus at least delta*B yields at least delta/4 of actual cube origins whose actual short-line means have modulus at least delta*B/2. This proves the initial actual bounded-observable short-line averaging/density step in the equal-side correction.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
remaining += (
    ' The initial actual equal-cube short-line mean approximation and delta/4 dense-origin step are now proved with explicit floor length and direction/error conditions. '
    'This is not a proof of quantitative Leibman: actual one-parameter character existence/uniform smoothness bounds, multivariate small-value coefficient estimates, common-character/direction extraction and bounded rational coefficient reconstruction still require proofs. '
    'The correction must keep its equal-side scope; no unsupported arbitrary rectangular quantitative theorem is introduced.')
review = [
    'Complex-valued averages are handled by their modulus and triangle inequalities. No invalid ordering or common phase of complex numbers is assumed. The dense-origin proof bounds the sum of actual norms by the low threshold times the entire original cube size plus B times the actual large-value set size; original mean normalization and B>0 are used before cancellation.',
    'The actual line shift is coordinatewise x_j+q_j*n with natural q_j<=L and n<M. Each actual translation error uses the already proved true uniform integer-box mass comparison. The absolute real shift is bounded by L*M. Commutation of actual finite averages then transports these shift estimates to original cube/line averages. A global pointwise bound on f is explicit, including shifted points outside the cube, as supplied by an original bounded nilmanifold observable.',
    'Actual natural floor division obeys (N/L^2)*L^2<=N, and positivity of the actual short line length follows from N>=L^2 and L>0. These imply L*floor(N/L^2)/N<=1/L. The explicit condition 8*card(kappa)<=delta*L gives error<=delta*B/4. Original obstruction>=delta*B therefore retains mean modulus>=3*delta*B/4, to which the genuine dense-value theorem applies.',
    'This formalizes only the initial averaging/density step, not the external one-parameter theorem or the subsequent inverse polynomial estimates. The primary correction source is https://arxiv.org/pdf/1311.6170v3, Section 3 Lemma 3.1. The OpenAI prescribed equal-cube route is retained; the main quantitative analytic input and complete original StrongConjecture remain open.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', lambda _: 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', lambda _: 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions corrected equal-cube analytic route: actual short-line averaging and dense origins, Green-Tao erratum v3 Section 3 Lemma 3.1; actual character existence and modular coefficient estimates remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual equal-cube short-line audit for', len(modules), 'modules.')
