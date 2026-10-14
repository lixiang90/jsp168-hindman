import Hindman168.RoughMvAffineCoefficient
import Mathlib.Tactic

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_translation_power_coefficient_top {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b : κ → R) (I J : κ → ℕ) (hJI : (∑ j, J j) ≤ ∑ j, I j) :
    roughAffinePowerCoefficient b (fun _ => 1) I J = if I=J then 1 else 0 := by
  by_cases hdom : ∀ j, I j ≤ J j
  · have he : I=J := by
      funext j
      by_contra hj
      have hstrict : I j < J j := lt_of_le_of_ne (hdom j) hj
      have hsum := Finset.sum_lt_sum (fun j _ => hdom j) ⟨j, Finset.mem_univ j, hstrict⟩
      omega
    subst J
    simp [roughAffinePowerCoefficient]
  · have hne : I ≠ J := by intro he; subst J; exact hdom (fun _ => le_rfl)
    rw [if_neg hne]
    push Not at hdom
    obtain ⟨j, hj⟩ := hdom
    unfold roughAffinePowerCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul, zero_mul]

theorem rough_translation_top_coefficient {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b : κ → R) (p : MvPolynomial κ R) (I : κ →₀ ℕ)
    (hI : p.totalDegree ≤ I.sum (fun _ e => e)) :
    coeff I (roughMvAffineSubstitution b (fun _ => 1) p) = coeff I p := by
  have he : Finsupp.equivFunOnFinite.symm (fun j => I j) = I := by ext j; simp
  conv_lhs => rw [← he]
  rw [rough_mv_affine_coefficient]
  have hI' : p.totalDegree ≤ ∑ j, I j := by
    have hsum : I.sum (fun _ e => e) = ∑ j, I j := Finsupp.sum_fintype _ _ (fun _ => rfl)
    exact hsum ▸ hI
  have hterms : ∀ J ∈ p.support,
      roughAffinePowerCoefficient b (fun _ => 1) (fun j => I j) J = if I=J then 1 else 0 := by
    intro J hJ
    have hJ' : (∑ j, J j) ≤ p.totalDegree := by
      have hsum : J.sum (fun _ e => e) = ∑ j, J j := Finsupp.sum_fintype _ _ (fun _ => rfl)
      exact hsum ▸ le_totalDegree hJ
    rw [rough_translation_power_coefficient_top b _ _ (hJ'.trans hI')]
    have hfun : (fun j => I j) = (fun j => J j) ↔ I=J := by
      constructor
      · intro h; ext j; exact congrFun h j
      · intro h; subst J; rfl
    simp only [hfun]
  have hsum : (∑ J ∈ p.support, coeff J p *
      roughAffinePowerCoefficient b (fun _ => 1) (fun j => I j) J) =
      ∑ J ∈ p.support, coeff J p * (if I=J then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hterms J hJ]
  rw [hsum]
  rw [Finset.sum_eq_single I]
  · simp only [ite_true, mul_one]
  · intro J _ hJ
    rw [if_neg hJ.symm, mul_zero]
  · intro hI
    rw [notMem_support_iff.mp hI, zero_mul]

theorem rough_translation_difference_degree {κ R : Type*} [Fintype κ] [CommRing R]
    (b : κ → R) (p : MvPolynomial κ R)
    (hne : roughMvAffineSubstitution b (fun _ => 1) p-p ≠ 0) :
    (roughMvAffineSubstitution b (fun _ => 1) p-p).totalDegree < p.totalDegree := by
  let d := roughMvAffineSubstitution b (fun _ => 1) p-p
  have hs : d.support.Nonempty := by
    exact support_nonempty.mpr hne
  obtain ⟨I, hI, hmax⟩ := Finset.exists_mem_eq_sup d.support hs (fun I => I.sum (fun _ e => e))
  have hlt : I.sum (fun _ e => e) < p.totalDegree := by
    by_contra! hge
    have hz : coeff I d = 0 := by
      dsimp [d]
      rw [coeff_sub, rough_translation_top_coefficient b p I hge, sub_self]
    exact (mem_support_iff.mp hI) hz
  simpa only [d, totalDegree, hmax] using hlt

end Hindman168
