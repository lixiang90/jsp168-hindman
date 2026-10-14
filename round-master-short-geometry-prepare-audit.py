from pathlib import Path
import re
p='round-master-short-geometry'
s=Path('round-full-window-short-gowers-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-full-window-short-gowers'",f"PREFIX = '{p}'").replace("OLD = 'round-aligned-global-gowers'","OLD = 'round-full-window-short-gowers'")
counts={'1059':'1061','1061':'1062','1043':'1044','1052':'1053','4942':'4945'}
s=re.sub(r'\b(?:1059|1061|1043|1052|4942)\b',lambda m:counts[m[0]],s)
s=s.replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/MasterPredictionShortCubeGeometry.lean']
components=['Divisibility M|P|R gives the exact full factorization M*((P/M)*(R/P))=R and coefficient equality M*(P/M)=P.','The actual master gap gives arbitrarily large short quotient lengths uniformly over all nonzero polynomial evaluations on the same prime pool. For tested polynomials this yields positive actual quotient factors and a nonempty short interval, together with the exact original width and shift-coefficient identities.']
remaining='The actual master prediction modulus now supplies uniformly positive quotient factors and short lengths, plus the exact width and shift-coefficient equalities needed by the full-window bound. The final combined master Gowers specialization remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The factorization lemma uses exact natural divisibility and retains the full interval width, not just its quotient by M.','Uniform short-length growth derives its polynomial cap from the actual prime-pool support, the original auxiliary lower bound and modulus domination. It does not assume a cap or a length bound as extra input.','The lower bound can be any natural B and holds uniformly after one stage threshold for all allowed x with nonzero evaluation.','For polynomials in the original tested family, existing prediction-modulus divisibility gives positive factors P/M and R/P and the exact identities needed by the finite full-window theorem.','Three new theorems are individually kernel audited. The final full master specialization and deep Bessel/inverse inputs remain unfinished.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
