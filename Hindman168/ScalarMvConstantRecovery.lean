import Hindman168.ScalarMvNaturalMultiples
import Hindman168.RoughBoxCharacterFixedSupport
import Hindman168.IntegerWeightedModOneNorm

namespace Hindman168
open scoped BigOperators Classical

theorem scalar_mv_integer_monomial_bound {κ : Type*} [Fintype κ]
    (x : κ → ℤ) (N : ℕ) (hx : x ∈ scalarMvIntegerCube κ N) (I : κ → ℕ) :
    |((∏ j, (x j)^(I j) : ℤ) : ℝ)| ≤ (N : ℝ)^(∑ j, I j) := by
  rw [Int.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun j _ => abs_nonneg _)
  intro j _
  have hb := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx j)
  have hx0 : (0 : ℝ) ≤ x j := by exact_mod_cast hb.1
  have hxN : (x j : ℝ) ≤ N := by exact_mod_cast hb.2.le
  rw [Int.cast_pow, abs_pow, abs_of_nonneg hx0]
  exact pow_le_pow_left₀ hx0 hxN _

/-- Recover the ORIGINAL constant from one ACTUAL original cube sample,
using the SAME multiplier and actual INTEGER monomial weights. -/
theorem scalar_mv_small_value_constant_recovery {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D N q : ℕ) (hp : p.totalDegree ≤ D)
    (x : κ → ℤ) (hx : x ∈ scalarMvIntegerCube κ N) (ε C : ℝ)
    (hsmall : ‖scalarMvCircleOrbit p x‖ ≤ ε)
    (hcoeff : ∀ I : κ → ℕ, 0 < (∑ j, I j) → (∑ j, I j) ≤ D →
      (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ C*ε) :
    ‖(((q : ℝ)*MvPolynomial.coeff 0 p : ℝ) : UnitAddCircle)‖ ≤
      (q : ℝ)*ε+((roughSpatialDegreeIndices κ D).card : ℝ)*C*ε := by
  let S := roughSpatialDegreeIndices κ D
  let w := fun I : κ → ℕ => ∏ j, (x j)^(I j)
  let v := fun I : κ → ℕ => (q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p
  have heval : MvPolynomial.eval (fun j => (x j : ℝ)) p = MvPolynomial.coeff 0 p+
      ∑ I ∈ S, MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p*∏ j, (x j : ℝ)^(I j) := by
    have h := congrArg (MvPolynomial.eval (fun j => (x j : ℝ))) (rough_fixed_spatial_expansion p D hp)
    simp only [map_add, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.coe_equivFunOnFinite_symm] at h
    exact h
  have hsumid : (∑ I ∈ S, (w I : ℝ)*v I) =
      (q : ℝ)*∑ I ∈ S, MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p*
        ∏ j, (x j : ℝ)^(I j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [w, v]
    push_cast
    ring
  have heq : (q : ℝ)*MvPolynomial.coeff 0 p =
      (q : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ)) p-∑ I ∈ S, (w I : ℝ)*v I := by
    rw [heval, hsumid]
    ring
  have hsample : ‖(((q : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤
      (q : ℝ)*ε := (mod_one_natural_multiplier_norm_le q _).trans
        (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg q))
  have hsum : ‖((∑ I ∈ S, (w I : ℝ)*v I : ℝ) : UnitAddCircle)‖ ≤ (S.card : ℝ)*C*ε := by
    apply (integer_weighted_mod_one_norm_bound S w v).trans
    calc
      _ ≤ ∑ _I ∈ S, C*ε := by
        apply Finset.sum_le_sum
        intro I hI
        have hb := (rough_spatial_degree_indices_mem D I).mp hI
        have hw := scalar_mv_integer_monomial_bound x N hx I
        exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (hcoeff I hb.1 hb.2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [heq, AddCircle.coe_sub]
  exact (norm_sub_le _ _).trans (add_le_add hsample hsum)

end Hindman168
