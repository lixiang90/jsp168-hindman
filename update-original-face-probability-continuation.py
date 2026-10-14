from pathlib import Path
import json
prefix='round-alignment-original-face-probability'
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
summary=json.loads(Path(prefix+'-checks.json').read_text(encoding='utf-8'))
p=Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt')
s=p.read_text(encoding='utf-8')
s=s.replace('Continuation after round-alignment-integer-face-state','Continuation after '+prefix,1)
completed="""ORIGINAL MARGINAL PRODUCT FACE PROBABILITY, NOW PROVED:
AlignmentOriginalProductFaceFailure is LITERAL original cube mean at original
slots vs original own-face shifted slots; it retains ALL original permitted
boxes/residues and observer choices AFTER the sampled tuple.
AlignmentOriginalProductFacePosterior proves actual conditional failure
vanishes by BOTH original removal errors (epsilon/3, delta/2) and genuine
terminal face error. Raw support/key identities identify SAME origin Y,
endpoints, selected denominator remainder and normalization. No conditional
independence. Native data/array determining evaluations/bases are explicit
proof parameters even though the final literal event omits them.
AlignmentOriginalProductFaceFiniteFamily gives ONE cutoff for arbitrary fixed
finite original own-pair/coordinate/profile/slot/observer lists. Empty lists
stay empty and source formulae remain selectable after width/exposed anchor.
AlignmentOriginalProductAllFacesPosterior instantiates the FULL fixed finite
list: actual own-pair subtype x ALL coordinates x ALL Fin 2 vertex profiles.
Exact integer zero/one representation covers any sample-selected profile or
failing face AFTER y. No unbounded integer-weight union is made.
FiniteTypicalExposureEventBound integrates actual good-key conditional caps
through EXACT original exposure disintegration. Original total and bad-key
mass remain; no bad-key positive likelihood or artificial probability.
AlignmentOriginalProductAllFacesGlobal uses PROVED actual bad-key vanishing
and key-good/typical identity. Original global all-face failure vanishes
uniformly BEFORE arbitrary exposed-key source maps. On conditional support,
sampled formula selections equal fixed key selections. Width/key-dependent
formulae are covered; unexposed-factor-dependent selections are NOT claimed.
AlignmentOriginalProductFacePositiveSelection gives genuine original global
failure zero limit for arbitrary width-varying key formulae, preserves it
under ANY additional probability-bounded-below conditioning, and chooses
supported original samples in prescribed positive-mass sets with all own
faces and zero/one profiles good for the fixed numerical condition.
These assertions concern ORIGINAL PRODUCT OBSERVATIONS. Full marginal
continuous cube test classes, countable simultaneity and local cube-coset
limits/face lift/full Alignment are still work, not supplied by these caps.

"""
s=s.replace('NEXT MAIN ROUTE:\n',completed+'NEXT MAIN ROUTE:\n',1)
a=s.index('1. Combine BOTH original-to-terminal removal comparisons with face error.')
z=s.index('2. Separate GTZ interval Gowers correlation inverse',a)
s=s[:a]+"""1. Complete marginal cube test interface / countable diagonal / local limits.
   Original PRODUCT-observation marginal all-face failure is PROVED under
   actual posterior and original global raw law. ALL own pairs, coordinates,
   zero/one profiles, original boxes/residues/tests are covered. Source
   formulae may vary with width and actual exposed key. Positive-mass extra
   conditioning preserves failure zero and yields supported original samples.
   Do NOT redo integer-state, face automorphism, finite profile lists, BOTH
   removal comparisons, exposure disintegration or global probability caps.
   Promote products to original complete marginal continuous cube tests via
   genuine finite product-span density/approximation on compact quotient
   cube spaces, or equivalent weak-law reasoning. Numerical observer bounds
   for fixed finite approximants precede sources and posterior samples; do
   not infer numeric Lipschitz of projections/slot automorphisms from continuity.
   Then enumerate original integer modulus, dimension <=s+1, endpoint and
   side bounds, observer bounds, tolerances and targets; finite-prefix union
   estimates + SlowStageDiagonal give ONE original supported sequence inside
   prescribed sets of probability bounded away from zero. Defaults at early
   invalid widths must not assert analytic truths. Preserve original master
   and model/data-selection dependencies; unexposed-factor-dependent source
   choices are not licensed by the current global cap.
   Pass to genuine original local cube-law limits/cosets, use own-face
   invariance through s+1 and face lift. Establish MARGINAL invariance only,
   preserving unrelated component limitations. Full Alignment synthesis and
   final positive distinct rapidly separated common-color FS/FP remain.

"""+s[z:]
s=s[:s.index('LATEST TERMINAL AUDIT,')]+ 'LATEST TERMINAL AUDIT, 2026-10-14: '+prefix+'.\n'+json.dumps(summary,indent=2)+'\n'
s+='This goal turn added '+str(manifest['last_round']['new_module_count'])+' modules, '+str(summary['new_theorems'])+' theorems and '+str(summary['new_definitions'])+' definitions in one terminal author audit round.\n'
s+='Every prior registered proof and axiom set is unchanged. No audit/compiler process remains active after terminal completion.\n'
s+=manifest['last_round']['remaining']+'\n'
p.write_text(s,encoding='utf-8')
print(prefix)
