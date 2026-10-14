import Hindman168.NativeRationalNonlinearSmallRationalFactors
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

theorem native_rational_nonlinear_right_factors {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 2 ≤ j) (hjL : j ≤ ℓ) (y : D.E) (hy : y ∈ L.layer j)
    (hFy : nativeRationalDifferenceExtension D L χ y=1)
    (hHigher : L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker)
    (q M N : ℕ) (hq : 0 < q) (hM : 0 < M) (hN : 0 < N)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ)
    (B : ℝ) (hB : 0 ≤ B)
    (hBounds : ∀ i : ℕ, 2 ≤ i → i ≤ ℓ → (N : ℝ)^i*
      ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff i : ℝ) : UnitAddCircle)‖ ≤ B) :
    let K := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
    ∃ (z : ℕ → ℤ) (E : ℝ[X]) (pK : RoughVectorMvPolynomial Unit D.E),
      E.natDegree ≤ j ∧ E.coeff 0=0 ∧ E.coeff 1=0 ∧
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ B) ∧
      RoughVectorMvWeightedDegree K.layer pK 0 ∧ RoughVectorMvDegreeLE pK ℓ ∧
      (∀ t : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => t)) =
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y)) ∧
      (∀ (x t H : ℝ), 0 ≤ H → |x| ≤ (N : ℝ) → |t| ≤ (N : ℝ) → |x-t| ≤ H →
        (M : ℝ)*|E.eval x-E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*B*(H/(N : ℝ))) ∧
      (∀ t : ℝ, |t| ≤ (N : ℝ) → |E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*B) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ))) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (n : ℝ) • y)*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ)))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      ∀ a t : ℕ,
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval ((a+M*q*t : ℕ) : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ) := by
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
