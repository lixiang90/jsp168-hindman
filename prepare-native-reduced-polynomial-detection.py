from pathlib import Path

original = Path('Hindman168/NativeBasepointTerminalPairDetection.lean').read_text(encoding='utf-8')
declaration = original[original.index('namespace Hindman168'):original.index(' := by')]
declaration = declaration.replace('native_basepoint_terminal_pair_uniform_detection',
    'native_basepoint_reduced_polynomial_uniform_detection')
old = '''(fun n => nativeRelativeReductionFactorMap D d hd
                  (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
                    (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ))'''
new = '''(fun n => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
                  (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n))'''
assert declaration.count(old) == 1
declaration = declaration.replace(old,new)
body = original.split(' := by',1)[1]
instances = body[:body.index('  letI : CompactSpace')]
proof = '''  obtain ⟨K,hK,θ,hθ,P,hP,hDetect⟩ := native_basepoint_terminal_pair_uniform_detection D d hd hdeg k hk η hη
  refine ⟨K,hK,θ,hθ,P,hP,?_⟩
  intro p hp h
  obtain ⟨r,hr,γ0,hγ0,t,ht,γh,hγh,hOrig⟩ := hDetect p hp h
  refine ⟨r,hr,γ0,hγ0,t,ht,γh,hγh,?_⟩
  intro a F hF hLarge
  obtain ⟨H,hH,hδ⟩ := hOrig a F hF hLarge
  refine ⟨H,hH,?_⟩
  have he : (fun n : ℤ => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n)) =
      (fun n => nativeRelativeReductionFactorMap D d hd
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) := by
    funext n
    exact native_basepoint_reduced_polynomial_orbit D d hd p hp r t h n
  rw [he]
  exact hδ

end Hindman168
'''
source = '''import Hindman168.NativeBasepointReducedPolynomial
import Hindman168.NativeBasepointTerminalPairDetection

/-! ONE FIXED actual reduced UNIT family detects original terminal derivative
means on the ACTUAL constructed reduced polynomial orbit. All actual relative
coefficient membership/orbit compatibility inputs are discharged. -/

''' + declaration + ' := by' + instances + proof
target = Path('Hindman168/NativeBasepointReducedPolynomialDetection.lean')
if target.exists():
    assert target.read_text(encoding='utf-8') == source
    print('Retained '+str(target))
else:
    target.write_text(source,encoding='utf-8')
    print('Created '+str(target))
