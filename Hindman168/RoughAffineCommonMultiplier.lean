import Hindman168.RoughBoxCharacterFixedSupport
import Hindman168.FiniteCoefficientScaleTransfer
import Hindman168.ModOneNaturalMultiplier

/-! A SINGLE positive NATURAL step^degree multiplier recovers ALL original
positive coefficients from actual affine child coefficients. Signed integer
translation and true retained length are explicit; circle norms are never
divided by the step. -/
namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_affine_substitution_comp {κ : Type*}
    (u k v h : κ → ℝ) (p : MvPolynomial κ ℝ) :
    roughMvAffineSubstitution v h (roughMvAffineSubstitution u k p) =
      roughMvAffineSubstitution (fun i => u i+k i*v i) (fun i => k i*h i) p := by
  have hc : (roughMvAffineSubstitution v h).comp (roughMvAffineSubstitution u k) =
      roughMvAffineSubstitution (fun i => u i+k i*v i) (fun i => k i*h i) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [roughMvAffineSubstitution]
    · intro i
      simp only [RingHom.comp_apply,roughMvAffineSubstitution,MvPolynomial.eval₂Hom_X',
        map_add,map_mul,MvPolynomial.eval₂Hom_C]
      ring
  exact RingHom.congr_fun hc p

theorem rough_affine_zero_power_coefficient {κ : Type*} [Fintype κ]
    (P : ℝ) (I J : κ → ℕ) :
    roughAffinePowerCoefficient (fun _ => 0) (fun _ => P) I J =
      if I=J then P^(∑ i, I i) else 0 := by
  by_cases he : I=J
  · subst J
    simp [roughAffinePowerCoefficient, Finset.prod_pow_eq_pow_sum]
  · rw [if_neg he]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    unfold roughAffinePowerCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hij : I i ≤ J i
    · have hlt : I i < J i := lt_of_le_of_ne hij hi
      simp [ne_of_gt (Nat.sub_pos_of_lt hlt)]
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hij)]

theorem rough_affine_zero_coefficient {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (P : ℝ) (I : κ → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun _ => 0) (fun _ => P) p) =
        P^(∑ i, I i)*coeff (Finsupp.equivFunOnFinite.symm I) p := by
  rw [rough_mv_affine_coefficient]
  simp_rw [rough_affine_zero_power_coefficient]
  have he (J : κ →₀ ℕ) : I=(fun i => J i) ↔ Finsupp.equivFunOnFinite.symm I=J := by
    constructor
    · intro h
      ext i
      simpa using congrFun h i
    · intro h
      funext i
      have hi := congrArg (fun t : κ →₀ ℕ => t i) h
      simpa using hi
  simp_rw [he]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm I)]
  · simp [mul_comm]
  · intro J _ hJ
    simp [hJ.symm]
  · intro hI
    simp [notMem_support_iff.mp hI]

theorem rough_affine_uniform_coefficient {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (b : κ → ℝ) (P : ℝ) (I : κ → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution b (fun _ => P) p) =
        P^(∑ i, I i)*coeff (Finsupp.equivFunOnFinite.symm I)
          (roughMvAffineSubstitution b (fun _ => 1) p) := by
  have hc := rough_affine_substitution_comp b (fun _ => 1) (fun _ => 0) (fun _ => P) p
  simp only [mul_zero,add_zero,one_mul] at hc
  rw [← hc,rough_affine_zero_coefficient]

theorem rough_affine_common_multiplier_coefficient {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (b : κ → ℝ) (P d : ℕ) (I : κ → ℕ)
    (hI : (∑ i, I i) ≤ d) :
    ((P^d : ℕ) : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution b (fun _ => 1) p) =
    ((P^(d-∑ i, I i) : ℕ) : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution b (fun _ => (P : ℝ)) p) := by
  rw [rough_affine_uniform_coefficient p b (P : ℝ) I, Nat.cast_pow,Nat.cast_pow,
    ← mul_assoc,← pow_add,Nat.sub_add_cancel hI]

end Hindman168
