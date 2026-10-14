from pathlib import Path

src=Path('Hindman168/NativeRationalNonlinearSmallRationalFactors.lean').read_text(encoding='utf-8')
a=src.index('theorem native_rational_nonlinear_small_rational_factors')
header=src[a:src.index(' := by',a)]
header=header.replace('native_rational_nonlinear_small_rational_factors','native_rational_nonlinear_right_factors')
needle='''          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y)*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t)))'''
replacement='''          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y))'''
assert header.count(needle)==1
header=header.replace(needle,replacement)
whole='''      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ))) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (n : ℝ) • y)*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ)))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
'''
needle='      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),'
assert header.count(needle)==1
header=header.replace(needle,whole+needle)
imports='''import Hindman168.NativeRationalNonlinearSmallRationalFactors
import Hindman168.NativeRationalKernelConjugateSource
import Hindman168.ScalarUnitPolynomialInverse

/-! Actual rational conjugation moves gamma to the RIGHT while retaining
TRUE smaller-filtration weights and degree. Finite original lattice residues
now apply to ACTUAL full orbit samples, with bounded error still variable.
No error freezing or large child correlation is inferred. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

'''
body=''' := by
  let F := nativeRationalDifferenceExtension D L χ
  have hF := native_rational_difference_extension_kills_commutator D L χ hHor.2.1 hzero
  have hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ r : ℚ, F v=(r : ℝ) :=
    fun v hv => native_rational_difference_extension_rational_value D L χ hHor.2.2 ⟨v,hv⟩
  obtain ⟨z,E,pK,hED,h0,h1,hSmall,hWeighted,_hDegree,hExact,hVar,hValue,hResidues,hPeriod⟩ :=
    native_rational_nonlinear_small_rational_factors D L χ hHor hzero p hp j hj hjL y hy hFy hHigher
      q M N hq hM hN hpow B hB hBounds
  let R := scalarNonlinearRationalPart j M z
  let Rmv := scalarUnitMvPolynomial R
  let pK' := nativeRationalKernelConjugateSource D Rmv y pK
  obtain ⟨hWeighted',hDegree'⟩ := native_rational_kernel_conjugate_source_weighted_degree D L F hF hRat
    Rmv j (scalar_unit_mv_polynomial_degree R j (scalar_nonlinear_rational_part_degree j M z)) y hy pK hWeighted
  have hConjugate (t : ℝ) :
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK' (fun _ => t))=
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (R.eval t • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))*
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (R.eval t • y))⁻¹ := by
    have he := native_rational_kernel_conjugate_source_exponential D Rmv y pK (fun _ => t)
    rw [scalar_unit_mv_polynomial_eval] at he
    exact he
  have hRight (t : ℝ) :
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p (fun _ => t))=
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK' (fun _ => t))*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (R.eval t • y) := by
    rw [hExact,hConjugate]
    dsimp only [R]
    group
  refine ⟨z,E,pK',hED,h0,h1,hSmall,hWeighted',hDegree',hRight,hVar,hValue,?_,hResidues,hPeriod⟩
  intro n
  obtain ⟨m,hm,he⟩ := hResidues n
  refine ⟨m,hm,?_⟩
  calc
    _ = (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (n : ℝ) • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) pK' (fun _ => (n : ℝ)))*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (R.eval (n : ℝ) • y) : D.G ⧸ D.Γ) :=
      congrArg (fun g : D.G => (g : D.G ⧸ D.Γ)) (hRight (n : ℝ))
    _ = _ := congrArg (fun q0 : D.G ⧸ D.Γ =>
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (n : ℝ) • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) pK' (fun _ => (n : ℝ)))) • q0) he

end Hindman168
'''
Path('Hindman168/NativeRationalNonlinearRightFactors.lean').write_text(imports+header+body,encoding='utf-8')
