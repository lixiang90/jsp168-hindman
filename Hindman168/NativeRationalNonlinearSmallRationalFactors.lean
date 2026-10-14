import Hindman168.NativeRationalNonlinearOriginalCoefficients
import Hindman168.NativeRationalNonlinearityExactFactorization
import Hindman168.ScalarNonlinearSmallRationalSplit
import Hindman168.ScalarNonlinearSmallVariation
import Hindman168.NativeRationalPolynomialFiniteResidues

/-! ACTUAL raw removed scalar receives genuine small/rational factors from
the completed native Q tables. Exact source identity, kernel weights,
bounded error variation and TRUE finite rational residues are retained.
No large child correlation or right-quotient transport is assumed. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_raw_nonlinear_small_rational_split {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 2 ≤ j) (hjL : j ≤ ℓ)
    (hHigher : L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker)
    (M N : ℕ) (hM : 0 < M) (B : ℝ)
    (hBounds : ∀ i : ℕ, 2 ≤ i → i ≤ ℓ → (N : ℝ)^i*
      ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff i : ℝ) : UnitAddCircle)‖ ≤ B) :
    let Q := scalarUnitPolynomial (unitMvNonlinearPart (roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap p))
    ∃ (z : ℕ → ℤ) (E : ℝ[X]), Q=E+scalarNonlinearRationalPart j M z ∧ E.natDegree ≤ j ∧
      E.coeff 0=0 ∧ E.coeff 1=0 ∧ ∀ i : ℕ, 2 ≤ i → i ≤ j →
        (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ B := by
  let Q := scalarUnitPolynomial (unitMvNonlinearPart (roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap p))
  have hDegree : Q.natDegree ≤ j := scalar_unit_polynomial_degree _ j
    (unit_mv_nonlinear_part_degree _ j (by omega)
      (native_rational_functional_scalar_degree D L p hp _ j hHigher))
  have hRaw : ∀ i : ℕ, 2 ≤ i → i ≤ j → (N : ℝ)^i*‖(((M : ℝ)*Q.coeff i : ℝ) : UnitAddCircle)‖ ≤ B := by
    intro i hi hij
    rw [native_rational_raw_nonlinear_high_coefficient D L χ hχ hzero p hp i hi]
    exact hBounds i hi (hij.trans hjL)
  exact scalar_nonlinear_small_rational_split Q j M N B hDegree
    (unit_mv_nonlinear_part_zero_coefficient _) (unit_mv_nonlinear_part_one_coefficient _) hM hRaw

theorem native_rational_nonlinear_small_rational_factors {s ℓ : ℕ}
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
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y)*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))) ∧
      (∀ (x t H : ℝ), 0 ≤ H → |x| ≤ (N : ℝ) → |t| ≤ (N : ℝ) → |x-t| ≤ H →
        (M : ℝ)*|E.eval x-E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*B*(H/(N : ℝ))) ∧
      (∀ t : ℝ, |t| ≤ (N : ℝ) → |E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*B) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      ∀ a t : ℕ,
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval ((a+M*q*t : ℕ) : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ) := by
  let F := nativeRationalDifferenceExtension D L χ
  have hF := native_rational_difference_extension_kills_commutator D L χ hHor.2.1 hzero
  have hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ r : ℚ, F v = (r : ℝ) :=
    fun v hv => native_rational_difference_extension_rational_value D L χ hHor.2.2 ⟨v,hv⟩
  obtain ⟨z,E,hSplit,hDegree,h0,h1,hSmall⟩ := native_rational_raw_nonlinear_small_rational_split
    D L χ hHor.2.1 hzero p hp j hj hjL hHigher M N hM B hBounds
  obtain ⟨hWeighted,hPolyDegree⟩ := native_rational_kernel_exact_residual_weighted_degree D L F hF hRat
    p hp j (by omega) y hy hFy hHigher
  let pK := nativeRationalKernelExactResidual D F p y
  refine ⟨z,E,pK,hDegree,h0,h1,hSmall,hWeighted,hPolyDegree,?_,
    scalar_nonlinear_small_variation E j M N B hDegree h0 h1 hN hB hSmall,
    scalar_nonlinear_small_value_bound E j M N B hDegree h0 h1 hM hN hB hSmall,
    native_rational_polynomial_finite_residue D j M q z y hM hq hpow,
    fun a t => native_rational_polynomial_progression_coset D j M q a t z y hM hpow⟩
  intro t
  have hScalar := congrArg (Polynomial.eval t) hSplit
  rw [eval_add,scalar_unit_polynomial_eval] at hScalar
  have hExp : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (MvPolynomial.eval (fun _ => t) (unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)) • y) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y) :=
    (congrArg (fun r : ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (r • y)) hScalar).trans
      (nativeLieExponential_add_smul (E := D.E) (I := D.I) (G := D.G) y _ _)
  exact (native_rational_kernel_exact_factorization D F p y (fun _ => t)).trans
    (congrArg (fun g : D.G => g*nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) pK (fun _ => t))) hExp)

end Hindman168
