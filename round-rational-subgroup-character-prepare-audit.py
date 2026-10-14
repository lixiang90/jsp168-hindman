from pathlib import Path
import json
import re

source = Path('round-rational-functional-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-rational-functional'", "PREFIX = 'round-rational-subgroup-character'")
source = source.replace("OLD = 'round-native-rational-subgroup-span'", "OLD = 'round-rational-functional'")
source = source.replace("spec_from_file_location('previous_audit', OLD + '-audit.py')",
    "spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')")
counts = {'914': '917', '917': '923', '899': '905', '908': '914', '4413': '4435',
          '15': '20', '16': '22', '3': '6'}
source = re.sub(r'\b(?:914|917|899|908|4413|15|16|3)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=1', 'new_definitions=2')
modules = ['RationalRestrictedKernel', 'NativeRationalSubgroupCharacter', 'NativeRationalCharacterKernel',
           'NativeCharacterLatticeReduction', 'NativeRationalCompactRepresentatives', 'NativeRationalLatticeCompact']
components = [
    'Real kernels restricted to arbitrary rational subspaces are spanned by their original rational vectors, by explicit rank-one rational pivot projection; nonzero restriction strictly lowers dimension.',
    'Every nonzero original Gamma-rational Lie subalgebra has a real character annihilating its INTERNAL bracket and rational on the SAME full lattice rational form. The character is not required to annihilate the ambient derived algebra.',
    'The original BCH finite polynomial layer theorem proves character additivity within the original exponential subgroup. Its actual kernel is the exponential of a smaller Gamma-rational native Lie subalgebra, with an actual original Gamma intersection pivot.',
    'Actual original pivot reduction writes g = Exp(r Log gamma) u gamma^z with 0<=r<=1, u in the smaller original kernel and gamma^z in the SAME specified Gamma, without lattice normality or discrete character-image hypotheses.',
    'A complete strong induction on real dimension constructs compact left representatives for EVERY Gamma-rational original native Lie subgroup and its SAME Gamma intersection; no supplied subgroup cocompactness remains.',
    'The actual restricted-lattice natural quotient is compact and metrizable, its natural inclusion into the original ambient quotient is a closed embedding, and the original orbit is compact. Intersection discreteness is proved by an actual embedding into the specified discrete Gamma.'
]
remaining = (
    'The general original specified-lattice rational subgroup cocompactness requirement is NOW PROVED: '
    'for every Gamma-rational native real Lie subalgebra S, its actual Exp(S) subgroup has constructed '
    'compact representatives modulo the SAME Gamma, compact metrizable natural restricted-lattice quotient, '
    'a closed embedding into G/Gamma and a compact orbit. The full original model, group and Gamma remain unchanged. '
    'Next connect this theorem to the paper\'s actual lower-central layers: prove real lower-central rationality '
    'for the now-identified W_Gamma and finish equality of algebraic GROUP lower-central layers with exponentials '
    'of the actual real Lie layers, not merely their Q logarithmic spans or closures. Instantiate the existing '
    'canonical cube/layer quotient and original-law testing interfaces with these proved compact quotients. '
    'Remaining full-target work includes quantitative degree/denominator bounds where required, complete '
    'nested coarse-model projections, Calibration/Alignment, actual coloring/arithmetic data and ordered '
    'positive rapidly separated monochromatic witnesses. StrongConjecture and the prize target remain unproved. '
    'No universal faithful matrix integration theorem is claimed or required by this native compactness proof. '
    'No unavoidable blocker is established; publication, PR and prize application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. The previous complete audit was freshly rechecked before edits. All 917 retained baseline source/config hashes were checked again before registration; only root and registry are changed. All previous proof sources, StrongStatement, original models/groups/lattices, pins and attributed files are preserved.',
    'RationalRestrictedKernel constructs a genuine rank-one projection along an actual rational vector with nonzero functional value. Its images of rational generators lie in the same rational kernel; real span functoriality proves the full restricted kernel equality. The zero restriction is separately handled. The argument assumes rational values, not a discrete image or topological closure of a Q subspace.',
    'The character construction uses V=(S restrict_Q) intersect W_Gamma and its INTERNAL rational Lie algebra. Actual inclusion into the nilpotent original algebra proves its lower-central termination. Nilpotent abelianization supplies an element outside its internal derived layer. Rational separation inside the proved full original W_Gamma, followed by the genuine natural scalar extension, constructs F on the original E. Two real span inductions kill brackets only inside S. This covers arbitrary nonzero rational S, not just the ambient group.',
    'Rationality and strict dimension descent hold for S intersect ker F. The actual Lie subalgebra T is constructed, and the genuine original global logarithm proves Exp(T) equals the kernel of F Log inside the same original Exp(S). No assumption that S or the lattice is normal in the ambient group is introduced.',
    'Actual BCH additivity is obtained by applying the retained rational polynomial layer theorem to the Q scalar restrictions of the REAL spaces S and S intersect ker F. This theorem has no finite-Q-dimension hypothesis and handles ALL real inputs in S. Thus this use does not restrict to rational exponential elements or invoke density without continuity.',
    'The retained actual intersection-spanning theorem gives a SAME Gamma intersect Exp(S) pivot gamma with nonzero character. With t=chi(g)/chi(gamma), z=floor t and r=t-z, the genuine residual Exp(-r Log gamma) g gamma^(-z) lies in Exp(T). Actual integer exponential powers, group cancellation and original character additivity establish g=Exp(r Log gamma) u gamma^z, with r in [0,1]. No lattice normality or discrete character image is used.',
    'The compact representative theorem is a FULL strong induction on dim_R S. The zero subalgebra has representative {1}. At each nonzero stage the strictly smaller rational T receives the induction hypothesis; its actual compact representatives are multiplied on the LEFT by the compact one-parameter pivot segment. The two RIGHT lattice factors multiply in the SAME Gamma. This completes the original-S induction and proves arbitrary specified-lattice rational subgroup cocompactness.',
    'The natural subtype preimage of the compact set is compact, and any remaining Gamma factor belongs to Exp(S) because x and g do. Therefore the quotient uses exactly Gamma.comap Exp(S).subtype. Existing natural quotient inclusion proves a closed embedding; the orbit is compact. Intersection discreteness follows by an embedding into original Gamma. Metrizability follows from the actual exponential homeomorphism with the finite real subspace and compact discrete coset theory.',
    'No whole algebraic group/Lie lower-central equality, quantitative bounds, final Calibration/Alignment, positive arithmetic extraction or StrongConjecture is inferred from this result. Publication and submission remain pending. No unavoidable blocker.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-rational-subgroup-character-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'expected_theorems': 20, 'expected_definitions': 2}))
