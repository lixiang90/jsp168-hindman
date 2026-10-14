from pathlib import Path
import re

prefix='round-native-conditional-proportion'
old='round-native-cofinal-proportion'
source=Path(old+'-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX='"+old+"'", "PREFIX='"+prefix+"'")
source=source.replace("OLD='round-native-real-rough-proportion'", "OLD='"+old+"'")
source=source.replace(old+'-baseline.json',prefix+'-baseline.json')
source=source.replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
modules=['Hindman168/ResidualScaleVariation.lean','Hindman168/ConditionalProductFiberComparison.lean','Hindman168/AlignmentPosteriorFiberComparison.lean']
source=re.sub(r'^MODULES=.*$', 'MODULES='+repr(modules),source,count=1,flags=re.M)
components=[
 'Bounded actual normalized-scale variation is handled by inclusion of the SAME real-box residual complex bad events into a reference-scale event. Actual positive dyadic retained products derive the fixed factor 2^card independently of tuples and native model complexity; common finite-family budgets are proved unconditionally at the enlarged geometry bound.',
 'Exact uniform finite-event fractions, original product Fubini with support-restricted fibers, coordinate union bounds, actual conditionMass domination and convergence are proved. Positive normalizing mass is derived where needed; conditioned factors are never declared independent.',
 'The ACTUAL short-exposure master posterior now obeys the coordinate fiber union bound with constant 3*2^T.card, obtained from the already proved actual posterior domination before every event/model. Original raw support supplies nonempty dyadic residue windows and total-one product factors. Actual native source/geometry/growth instantiation of the fiber hypotheses remains separate.'
]
remaining='StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Unconditional native rough proportions cover real residual boxes, arbitrary cofinal widths, fixed finite native families and bounded varying normalized scales; actual short-exposure posterior Fubini/union comparison is proved. Remaining: actual master/native source, coarse residue, polynomial degree/log identities and reference-growth instantiation of native fiber caps; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence correlation inverse; full cube/Alignment synthesis and final positive distinct rapidly separated monochromatic FS/FP. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent kernel replay/external peer review. Repaired source slab estimate is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
source=re.sub(r'COMPONENTS=\[.*?\]\nREMAINING=', 'COMPONENTS='+repr(components)+'\nREMAINING=',source,count=1,flags=re.S)
source=re.sub(r"REMAINING='[^\n]*'",'REMAINING='+repr(remaining),source,count=1)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-baseline.json').write_bytes(Path('verification-manifest.json').read_bytes())
Path(prefix+'-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
Path(prefix+'-mathematical-review.txt').write_text(
 'JSP-000168 / Erdos #172, 2026-10-13. Partial overall coverage.\n'
 'Author checking, not independent replay or external peer review.\n\n'
 'Review follows the pinned original rough-step and conditional-probability route.\n'
 'The scale comparison retains every actual real endpoint, compatible residue,\n'
 'observable and discrepancy witness; only the admissible geometry envelope\n'
 'enlarges from C to C*K. The same finite-family uniform theorem discharges\n'
 'the reference comparison; no rough-comparison oracle is introduced.\n'
 'The dyadic product calculation proves q>0 and both reference-scale bounds\n'
 'from real positive scales and positive retained M; empty tails are valid.\n'
 'K=2^card is fixed before tuple/source/model inputs. This result does not\n'
 'yet derive reference-scale growth from actual master parameters.\n\n'
 'Uniform finite event equals filtered cardinality divided by support size;\n'
 'zero supports are handled algebraically, never called probabilities.\n'
 'A positive strict count bound forces a positive denominator. Original\n'
 'product probability derives from nonnegative factors of total one. Exact\n'
 'pivot-coordinate equivalence preserves all other coordinates; cap hypotheses\n'
 'are needed only on their ACTUAL product support. Finite union and fixed\n'
 'domination then give C0*card*epsilon and convergence, with coefficients\n'
 'fixed before events/models. Actual conditionMass uses a fixed positive\n'
 'conditioning-event lower bound, not conditional independence.\n\n'
 'The master posterior specialization discharges domination using the actual\n'
 'alignment_typicalShortPosterior_bound_eventually theorem. Each exposed\n'
 'dyadic residue window contains its actual positive raw-support anchor,\n'
 'so all factor totals are genuinely one. Fintype enumeration reconciliation\n'
 'uses congruence only; no new instance or option is declared. The resulting\n'
 '3*2^T.card depends on tail cardinality, not native model complexity.\n'
 'Actual native fiber-event bounds remain explicit uninstantiated hypotheses\n'
 'in this probability theorem, accurately separated from the unconditional\n'
 'native analytic comparison. This is progress, not completed Alignment.\n\n'
 'Original StrongConjecture remains unchanged and unproved. No custom axiom,\n'
 'sorry, unsafe/native shortcut, structure/instance/option bypass is added.\n'
 'Every previously registered proof source and axiom set must be preserved.\n\n'+remaining+'\n',encoding='utf-8')
print(prefix)
