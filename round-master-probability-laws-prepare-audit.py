from pathlib import Path
import re

source = Path('round-native-selected-models-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-native-selected-models'", "PREFIX = 'round-master-probability-laws'")
source = source.replace("OLD = 'round-alternating-indices'", "OLD = 'round-native-selected-models'")
counts = {'965':'967','967':'970','949':'952','958':'961','4661':'4674'}
source = re.sub(r'\b(?:965|967|949|958|4661)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=0', 'new_definitions=3').replace('new_instances=0', 'new_instances=1')
source = source.replace('new_theorems=4', 'new_theorems=9').replace('new_theorem_count=4', 'new_theorem_count=9')
source = source.replace("== 4\n    root", "== 9\n    root").replace("'theorem_count': 4", "'theorem_count': 9")
source = source.replace('len(set(names)) == 4', 'len(set(names)) == 13').replace('len(names) == 4', 'len(names) == 13')
source = source.replace('new_axiom_reports=4', 'new_axiom_reports=13').replace('new_selected_report_count=4', 'new_selected_report_count=13')
source = source.replace('new_module_count=2', 'new_module_count=3')
modules = ['Hindman168/HarmonicSubprobability.lean', 'Hindman168/SubprobabilityHilbertBounds.lean', 'Hindman168/MasterOriginalHilbertLaws.lean']
components = [
    'The exact original harmonic normalizer is nonnegative for every X,W. A zero normalizer gives the zero original integer mass; otherwise the original mass is a probability. Thus every stage is nonnegative with total mass zero or one, without repairing or replacing its definition.',
    'The genuine weighted L2 uniform bound and bounded-family construction now apply to total mass at most one. Pointwise clipping gives an actual bounded family and contracts distance in the original completed Hilbert space, including zero-mass stages.',
    'Actual original master integer masses provide bounded Hilbert families at all stages. Under MasterParameterConditions, one uniform eventual stage works for every master pivot and all corresponding total masses are one.'
]
remaining = ('The original harmonic law now has all-stage nonnegativity and mass at most one, including exact zero laws at zero normalizers. Subprobability L2 bounds and actual clipped Hilbert families are proved without replacing initial stages. Original master masses are uniformly probability laws eventually and support bounded Hilbert families at every stage. Next extend native clipped/selected-model assembly to these subprobability bounds, instantiate actual master gap maps, and assemble finite selected models with common bounds. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative estimates remain. StrongConjecture remains unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(modules) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous audit rechecked and all 967 baseline hashes verified at registration. Prior proof sources and original measure definitions remain unchanged.',
    'Audit identified that original-law validity was previously only eventual whereas selected-model interfaces required normalization at every stage. Rather than replace early laws, this increment proves the original laws themselves are subprobabilities at every stage.',
    'The normalizer is a finite sum of nonnegative inverse natural numbers. If zero, division by zero in the original Lean weight definition yields zero for every natural coordinate; negative integer coordinates already have zero mass. Otherwise existing positive-normalizer normalization applies.',
    'The norm bound is proved directly from the original weighted squared sum and total<=1. The clipping bounded family uses bound one; distance contraction follows from the actual ultralimit of original weighted squared distances. No positive-total assumption is introduced.',
    'The canonical nonnegativity Fact instance is backed by the unconditional original-mass theorem. All named instances, definitions and theorems are individually included in the kernel axiom audit.',
    'Master original bounded families retain the exact cutoff and primorial at every original stage, without reindexing or totalization. Uniform eventual normalization for every pivot follows from raw_cutoffs_valid and is extracted as one stage threshold.',
    'The native selected-model theorem still needs the subprobability generalization and concrete master-gap instantiation. No eventual claim is silently used as an all-stage hypothesis, and no completed target is claimed.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-master-probability-laws-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: 9 theorems, 3 definitions, 1 instance, 13 reports.')
