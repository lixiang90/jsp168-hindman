from pathlib import Path
import re
source=Path('round-cyclic-short-cube-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-cyclic-short-cube'", "PREFIX = 'round-master-cyclic-quotients'").replace("OLD = 'round-uniform-tuple-expectation'", "OLD = 'round-cyclic-short-cube'")
counts={'1022':'1024','1024':'1027','1006':'1009','1015':'1018','4851':'4858'}
source=re.sub(r'\b(?:1022|1024|1006|1015|4851)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=5','new_theorems=7').replace('new_theorem_count=5','new_theorem_count=7').replace('new_module_count=2','new_module_count=3')
source=source.replace('== 5\n    root','== 7\n    root').replace("'theorem_count': 5","'theorem_count': 7")
source=source.replace('len(set(names)) == 5','len(set(names)) == 7').replace('len(names) == 5','len(names) == 7').replace('new_axiom_reports=5','new_axiom_reports=7').replace('new_selected_report_count=5','new_selected_report_count=7')
modules=['Hindman168/CyclicScaleQuotients.lean','Hindman168/MasterCyclicQuotients.lean','Hindman168/MasterCyclicShortLengths.lean']
components=[
 'Exact scale arithmetic proves R/M=(P/M)(R/P), divisibility of P/M into R/M, the correct subgroup cardinality R/P, and the original short-length equality (R/P)/J=R/(JP) under the stated divisibility conditions.',
 'The original MasterParameterConditions polynomial gap divisibility supplies positivity, quotient divisibility, exact cyclic factorization and subgroup cardinality for every nonzero tested polynomial value on an actual prime-pool tuple.',
 'Actual master gap growth proves uniform eventual lower bounds on R/(JP) for all positive denominators satisfying a fixed polynomial cap JP<=S^k, including varying finite gap labels. Taking the lower bound one supplies nonempty short intervals.'
]
remaining='Exact cyclic quotient arithmetic, master polynomial-value subgroup geometry and uniform short-length lower bounds under a polynomial denominator cap are proved. Full template-denominator cap instantiation and the harmonic-to-periodized Haar comparison, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1024 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The quotient factorization uses actual divisibility witnesses and positive divisors, avoiding invalid cancellation of floor divisions. The subgroup cardinality follows from the previously proved explicit cyclic bijection.',
 'The short interval identity uses the exact nested natural-division law, retaining the denominator J*P and its floor.',
 'Master polynomial geometry is instantiated with the original evaluated integer polynomial absolute value and original pool-membership hypotheses. Nonzero evaluation proves its positivity; the existing master gap_polynomial_dvd supplies divisibility.',
 'The resulting subgroup lives in the original quotient modulus F.gap/F.modulus. Its size is the actual quotient by F.modulus times the polynomial absolute value.',
 'Uniform short-length lower bounds follow from the original gap PowerDominates condition with finite-choice gap labels. The eventual set is chosen before the positive denominator P, so the bound is uniform over all denominators satisfying the stated cap.',
 'Seven theorems in three modules are individually kernel audited. The denominator cap is explicit and has not yet been verified for every final template denominator. Harmonic periodization, Bessel and inverse inputs, and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-master-cyclic-quotients-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: seven theorems.')
