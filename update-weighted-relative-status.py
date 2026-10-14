from pathlib import Path
import json
prefix='round-native-rational-weighted-relative'
review=json.loads(Path(prefix+'-review.json').read_text(encoding='utf-8'))
c=review['verified']
assert not review['full_target_proved'] and c['standard_axioms_only']
text=f'''JSP-000168 / Erdos #172 -- 2026-10-13

Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction found.
Latest goal turn PROGRESS: actual proof source/build/axiom/hash evidence.

Latest audit: {prefix}
11 new modules: {c['new_theorems']} theorems, {c['new_definitions']} definitions.
All actual commands awaited terminal success. Author checking is not
independent kernel replay or external peer review.

NOW PROVED:
* ANY actual finite rational native Lie filtration F supports true native
  weighted multiplication, affine shifts and product/constant perturbations.
  Constants remain UNBOUNDED; F(0)=F(1)=top supplies actual constant weights.
  Actual real/integer filteredness uses genuine original brackets/Exp layers.
* ANY true weighted univariate source p with logarithmic p(0)=0 yields the
  ACTUAL normalized original integer pair in SAME genuine relative group.
  First-coordinate logarithmic polynomial is CONSTRUCTED; its difference
  from source p has ONE extra weight. EVERY aggregated coefficient has
  both coordinates in F(|J|) and their difference in F(|J|+1).
* ALL aggregated coefficients, including the constant, belong to ACTUAL
  relative native model: exact original integer pair Log compatibility and
  algebraic natural-grid coefficient recovery PROVE this membership.
  The actual subtype coefficient polynomial retains real evaluations,
  COMPLETE scalar polynomials and EVERY aggregate coefficient.
* SAME true relative weights, real/integer filteredness in ACTUAL internal
  relative group layers, original native integer exponentials and EVERY
  original nonnormal coset sample are PROVED. Removing zero vector terms
  gives ordinary degree at most ell, with NO invalid source termwise degree
  assumption for arbitrarily high-degree scalar terms with zero vectors.
* Actual relative polynomial feeds SAME true terminal quotient and ACTUAL
  degree-reduced NativeData. Output weights use ORIGINAL projected IMAGE
  layers; zero-trim degree is at most ell-1. EXACT original integer pair
  group projection/coset factor samples and COMPLETE scalar pullback survive.
* Both ACTUAL native basepoint normalization and actual linear lattice
  correction preserve ANY true rational Lie weights. Normalized logarithmic
  zero is PROVED using actual native Exp/Log inverses, and ordinary degree
  is at most ell after zero trimming. These lemmas apply at later actual
  projected IMAGE filtration stages with UNBOUNDED original constants.
* FULL weighted relative-then-terminal polynomial construction is APPLIED
  to ACTUAL twice-normalized ORIGINAL ordinary-degree <=d source. Every
  input weight and logarithmic-zero property is PROVED at SAME stretch d;
  output degree is s*d-1, with exact original normalized pair quotient
  samples. No inflated stretch s*d or substitute lattice is used.
* Retained: ACTUAL generic relative/terminal quotient geometry, true smooth
  projections/differentials/Exp/Log, rational actual image lattice/layers,
  complete finite GEOMETRIC recursion with bound ell-n and actual trivial
  group at ell stages. SAME original nilpotency-step bound s is unchanged.

VERIFIED:
* {c['project_modules']} own modules + {c['pntplus_modules']} attributed PNT+ modules.
* Full build: {c['build_jobs']} successful jobs; exact terminal log saved.
* {c['selected_axiom_reports']} selected axiom reports; ALL standard whitelist only.
* All retained proof sources and retained declaration axiom sets unchanged.
* No sorry/admit/custom axioms/native_decide/implemented_by or unsafe proof.
* Fixed Lean 4.32.2, mathlib commit and six pinned OpenAI source sections
  match retained hashes/source commit; all new sources/oleans are current.

PUBLICATION:
No public repository, PR or prize application yet. User-authorized publication
and application execute at actual FULL completion or genuine unavoidable
obstruction, with honest scope; partial lemmas do not qualify as full solution.

EXACT REMAINING WORK:
'''+review['remaining']+'\n'
Path('CURRENT-STATUS.txt').write_text(text,encoding='utf-8')
print(json.dumps({'status':'ACTIVE','audit':prefix,'counts':c}))
