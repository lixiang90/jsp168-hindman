from pathlib import Path
import re
source=Path('round-master-cyclic-quotients-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-master-cyclic-quotients'", "PREFIX = 'round-prediction-modulus-cap'").replace("OLD = 'round-cyclic-short-cube'", "OLD = 'round-master-cyclic-quotients'")
counts={'1024':'1027','1027':'1029','1009':'1011','1018':'1020','4858':'4864'}
source=re.sub(r'\b(?:1024|1027|1009|1018|4858)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=7','new_theorems=6').replace('new_theorem_count=7','new_theorem_count=6').replace('new_module_count=3','new_module_count=2')
source=source.replace('== 7\n    root','== 6\n    root').replace("'theorem_count': 7","'theorem_count': 6")
source=source.replace('len(set(names)) == 7','len(set(names)) == 6').replace('len(names) == 7','len(names) == 6').replace('new_axiom_reports=7','new_axiom_reports=6').replace('new_selected_report_count=7','new_selected_report_count=6')
modules=['Hindman168/MasterPredictionModulusCap.lean','Hindman168/MasterPredictionModulusGeometry.lean']
components=[
 'The original predictionCubeModulus, including its rough part and smooth factor, has a uniform polynomial cap on actual masterPrimeSlotsMass support under the original replica/prime-slot alignment and smooth-factor divisibility conditions.',
 'The cap is combined with actual master growth to prove arbitrary eventual lower bounds for the original predictionQuotientLength, uniformly over every supported nonzero prime tuple and every finite replica. The nonzero length no longer requires a separate denominator-cap hypothesis.',
 'The original prediction modulus absolute value divides the master gap by rough-part divisibility and the existing polynomial gap condition. When its smooth factor is the master modulus, it contains that modulus and satisfies the exact cyclic quotient factorization.'
]
remaining='Actual prediction-modulus polynomial caps and uniform quotient-length growth are now instantiated from prime support and slot alignment. Rough-part prediction moduli have proved master-gap divisibility and cyclic factorization with the full master smooth factor. The harmonic-to-periodized Haar comparison, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain, along with assembling all finite-model estimates into the subgroup inverse lemma. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1027 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The cap uses the existing exact predictionCubeModulus polynomial estimate. The smooth factor is bounded using its divisibility into the original positive master modulus, and only variables occurring in each polynomial use prime-slot alignment.',
 'Actual masterPrimeSlotsMass support supplies the prime-coordinate bounds. The exponent depends on J, the original polynomial coefficient size and total degree, not on the stage, prime tuple or master count.',
 'Uniform length growth intersects finitely many replica eventual sets before quantifying over supported prime tuples. Nonzero polynomial evaluation and positivity of the smooth factor prove the actual denominator is positive.',
 'The modulus divisibility proof preserves the rough part: it divides the original polynomial absolute value, so the smooth-factor times rough-part modulus divides the master-modulus times full value, which divides the gap by MasterParameterConditions.',
 'For the full master smooth factor, the prediction modulus contains the master modulus exactly as a factor. The cyclic quotient identity follows with all positivity and divisibility hypotheses proved from the original data.',
 'Six theorems in two modules are individually kernel audited. This supplies cap and length hypotheses for the actual template modulus but does not prove the harmonic periodization, Bessel or inverse conclusions, or the final target.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-prediction-modulus-cap-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: six theorems.')
