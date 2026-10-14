import Hindman168.NativeSubgroupHorizontalTaylor

/-! The highest scalar monomial coefficient is the actual original Taylor
coefficient divided by its factorial. Lower elimination steps cannot alter
it; all higher degrees vanish in the selected character kernel. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem scalar_binomial_polynomial_degree_le (j : ℕ) :
    (scalarBinomialPolynomial j).natDegree ≤ j :=
  (Polynomial.natDegree_C_mul_le _ _).trans_eq (descPochhammer_natDegree ℝ j)

theorem scalar_binomial_polynomial_top_coefficient (j : ℕ) :
    (scalarBinomialPolynomial j).coeff j = (j.factorial : ℝ)⁻¹ := by
  have h := (monic_descPochhammer ℝ j).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [scalarBinomialPolynomial, Polynomial.coeff_C_mul, h, mul_one]

theorem scalar_polynomial_initial_zeros_binomial (P : ℝ[X]) (j : ℕ)
    (hd : P.natDegree ≤ j) (hz : ∀ m : ℕ, m < j → P.eval (m : ℝ) = 0) :
    P = Polynomial.C (P.eval (j : ℝ)) * scalarBinomialPolynomial j := by
  let Q := P - Polynomial.C (P.eval (j : ℝ)) * scalarBinomialPolynomial j
  have hdeg : Q.natDegree ≤ j := (Polynomial.natDegree_sub_le _ _).trans
    (max_le hd ((Polynomial.natDegree_C_mul_le _ _).trans (scalar_binomial_polynomial_degree_le j)))
  have hi : Function.Injective (fun k : Fin (j+1) => (k.val : ℝ)) := by
    intro k l h
    exact Fin.ext (Nat.cast_injective h)
  have hv : ∀ k : Fin (j+1), Q.eval (k.val : ℝ) = 0 := by
    intro k
    dsimp only [Q]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, scalar_binomial_polynomial_eval_nat]
    by_cases hk : k.val = j
    · simp only [hk, Nat.choose_self, Nat.cast_one, mul_one, sub_self]
    · have hkj : k.val < j := by have := k.isLt; omega
      rw [hz k.val hkj, Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, mul_zero, sub_self]
  have he : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hi hv
    (by simpa only [Fintype.card_fin] using hdeg.trans_lt (Nat.lt_succ_self j))
  exact sub_eq_zero.mp he

theorem native_subgroup_taylor_lower_removals_preserve_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j k : ℕ) (hk : k ≤ j) :
    (scalarUnitPolynomial (roughVectorMvProjection phi (adaptedTaylorResidual D p k))).coeff j =
      (scalarUnitPolynomial (roughVectorMvProjection phi p)).coeff j := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hr := (native_rational_subgroup_taylor_residual_properties D F p hp k).1
      rw [adaptedTaylorResidual, native_subgroup_horizontal_taylor_removal D F phi hB _ hr,
        Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt
          ((scalar_binomial_polynomial_degree_le k).trans_lt (by omega : k < j)), mul_zero, sub_zero]
      exact ih (by omega)

theorem native_subgroup_taylor_top_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (j : ℕ) (hNext : F.layer (j+1) ≤ phi.ker)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    MvPolynomial.coeff (Finsupp.single () j) (roughVectorMvProjection phi p) =
      phi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) /
        (j.factorial : ℝ) := by
  let r := adaptedTaylorResidual D p j
  let P := scalarUnitPolynomial (roughVectorMvProjection phi r)
  have hr := native_rational_subgroup_taylor_residual_properties D F p hp j
  have hd : P.natDegree ≤ j := native_subgroup_horizontal_projection_degree D F phi j hNext r hr.1
  have hz : ∀ m : ℕ, m < j → P.eval (m : ℝ) = 0 := by
    intro m hm
    rw [scalar_unit_polynomial_eval, roughVectorMvProjection_eval, hr.2 m hm, map_zero]
  have he := congrArg (fun q : ℝ[X] => q.coeff j) (scalar_polynomial_initial_zeros_binomial P j hd hz)
  rw [Polynomial.coeff_C_mul, scalar_binomial_polynomial_top_coefficient,
    scalar_unit_polynomial_eval, roughVectorMvProjection_eval] at he
  rw [← scalar_unit_polynomial_coefficient,
    ← native_subgroup_taylor_lower_removals_preserve_coefficient D F phi hB p hp j j le_rfl]
  exact he.trans (div_eq_mul_inv _ _).symm

end Hindman168
