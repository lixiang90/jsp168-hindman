import Hindman168.RoughFixedSpatialSupport
import Hindman168.RoughVectorMvPolynomial

namespace Hindman168
open MvPolynomial
open scoped Classical

theorem rough_progression_option_right {κ R : Type*} [CommSemiring R]
    (P : Polynomial R) : optionEquivRight R κ (roughProgressionPolynomial P) = C P := by
  have h : (optionEquivRight R κ).toRingHom.comp
      (Polynomial.eval₂RingHom C (X none)) = (C : Polynomial R →+* MvPolynomial κ (Polynomial R)) := by
    apply Polynomial.ringHom_ext
    · intro r
      change optionEquivRight R κ (Polynomial.eval₂ C (X none) (Polynomial.C r)) = C (Polynomial.C r)
      rw [Polynomial.eval₂_C, optionEquivRight_C]
    · change optionEquivRight R κ (Polynomial.eval₂ C (X none) Polynomial.X) = C Polynomial.X
      rw [Polynomial.eval₂_X, optionEquivRight_X_none]
  exact RingHom.congr_fun h P

theorem rough_spatial_rename_option_right {κ R : Type*} [CommSemiring R]
    (P : MvPolynomial κ R) :
    optionEquivRight R κ (rename Option.some P) = map Polynomial.C P := by
  have h : (optionEquivRight R κ).toRingHom.comp (rename Option.some).toRingHom =
      map (Polynomial.C : R →+* Polynomial R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change optionEquivRight R κ (rename Option.some (C r)) = map Polynomial.C (C r)
      rw [rename_C, optionEquivRight_C, map_C]
    · intro i
      change optionEquivRight R κ (rename Option.some (X i)) = map Polynomial.C (X i)
      rw [rename_X, optionEquivRight_X_some, map_X]
  exact RingHom.congr_fun h P

theorem rough_joint_option_right {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (P0 : Polynomial R) (θ : (κ →₀ ℕ) → Polynomial R) :
    optionEquivRight R κ (roughSpatialJointPolynomial s P0 θ) =
      C P0+∑ I ∈ s, monomial I (θ I) := by
  simp only [roughSpatialJointPolynomial, map_add, map_sum, map_mul,
    rough_progression_option_right, rough_spatial_rename_option_right,
    map_monomial, map_one, C_mul_monomial, mul_one]

theorem rough_fixed_scalar_joint_expansion {κ R : Type*} [Fintype κ] [CommSemiring R]
    (p : MvPolynomial (Option κ) R) (q : ℕ) (hp : p.totalDegree ≤ q) :
    let θ := fun I => coeff I (optionEquivRight R κ p)
    p = roughSpatialJointPolynomial (roughSpatialDegreeSupport κ q) (θ 0) θ ∧
      (θ 0).natDegree ≤ q ∧
      ∀ I ∈ roughSpatialDegreeSupport κ q, (θ I).natDegree+I.sum (fun _ e => e) ≤ q := by
  intro θ
  have hsub := rough_option_right_support_fixed p q hp
  have hsum : ∑ I ∈ insert 0 (roughSpatialDegreeSupport κ q),
      monomial I (θ I) = optionEquivRight R κ p := by
    have h := Finsupp.sum_of_support_subset (AddMonoidAlgebra.coeff (optionEquivRight R κ p)) hsub
      (fun I r => monomial I r) (fun _ _ => monomial_zero)
    rw [sum_def] at h
    exact h.symm.trans (support_sum_monomial_coeff _)
  rw [Finset.sum_insert (rough_spatial_degree_support_zero q)] at hsum
  refine ⟨?_, ?_, ?_⟩
  · apply (optionEquivRight R κ).injective
    rw [rough_joint_option_right]
    simpa only [monomial_zero'] using hsum.symm
  · simpa only [Finsupp.sum_zero_index, add_zero] using
      rough_option_right_weighted_degree p 0 q hp (by simp)
  · intro I hI
    exact rough_option_right_weighted_degree p I q hp
      ((rough_spatial_degree_support_mem q I).mp hI).2

theorem rough_vector_scalar_joint_expansion {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (q : ℕ) (hp : RoughVectorMvDegreeLE p q) :
    ∃ (P0 : Polynomial ℝ) (θ : (κ →₀ ℕ) → Polynomial ℝ),
      P0.natDegree ≤ q ∧
      (∀ I ∈ roughSpatialDegreeSupport κ q, (θ I).natDegree+I.sum (fun _ e => e) ≤ q) ∧
      ∀ x : Option κ → ℝ, χ (roughVectorMvEval p x) =
        eval x (roughSpatialJointPolynomial (roughSpatialDegreeSupport κ q) P0 θ) := by
  let f := roughVectorMvProjection χ p
  let θ := fun I => coeff I (optionEquivRight ℝ κ f)
  obtain ⟨he, h0, hθ⟩ := rough_fixed_scalar_joint_expansion f q (roughVectorMvProjection_degree χ hp)
  refine ⟨θ 0, θ, h0, hθ, ?_⟩
  intro x
  rw [← roughVectorMvProjection_eval]
  exact congrArg (eval x) he

end Hindman168
