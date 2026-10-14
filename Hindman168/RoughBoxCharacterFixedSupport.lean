import Hindman168.RoughBoxCharacterTranslation
import Hindman168.RoughFixedSpatialSupport
import Hindman168.RoughIntegerTranslationInverse

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_spatial_support_fixed {κ R : Type*} [Fintype κ] [CommSemiring R]
    (p : MvPolynomial κ R) (q : ℕ) (hp : p.totalDegree ≤ q) :
    p.support ⊆ insert 0 (roughSpatialDegreeSupport κ q) := by
  intro I hI
  by_cases h0 : I = 0
  · simp [h0]
  · have hd := (le_totalDegree hI).trans hp
    have hs : I.sum (fun _ e => e) = ∑ j, I j := Finsupp.sum_fintype _ _ (fun _ => rfl)
    have hpos : 0 < I.sum (fun _ e => e) := by
      by_contra! h
      have hz : ∑ j, I j = 0 := by omega
      have hzj : ∀ j, I j = 0 := fun j => by
        have hj := Finset.single_le_sum (fun i _ => Nat.zero_le (I i)) (Finset.mem_univ j)
        omega
      exact h0 (Finsupp.ext hzj)
    exact Finset.mem_insert_of_mem ((rough_spatial_degree_support_mem q I).mpr ⟨hpos, hd⟩)

theorem rough_fixed_spatial_expansion {κ R : Type*} [Fintype κ] [CommSemiring R]
    (p : MvPolynomial κ R) (q : ℕ) (hp : p.totalDegree ≤ q) :
    p = C (coeff 0 p)+∑ J ∈ roughSpatialDegreeIndices κ q,
      monomial (Finsupp.equivFunOnFinite.symm J) (coeff (Finsupp.equivFunOnFinite.symm J) p) := by
  have hsum : ∑ I ∈ insert 0 (roughSpatialDegreeSupport κ q), monomial I (coeff I p) = p := by
    have h := Finsupp.sum_of_support_subset (AddMonoidAlgebra.coeff p) (rough_spatial_support_fixed p q hp)
      (fun I r => monomial I r) (fun _ _ => monomial_zero)
    rw [sum_def] at h
    exact h.symm.trans (support_sum_monomial_coeff _)
  rw [Finset.sum_insert (rough_spatial_degree_support_zero q)] at hsum
  simpa only [monomial_zero', roughSpatialDegreeSupport, roughFiniteMultiindices, Finset.sum_map,
    Equiv.toEmbedding_apply] using hsum.symm

theorem rough_box_character_fixed_translation {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (q : ℕ) (hp : p.totalDegree ≤ q)
    (b : κ → ℤ) (Z C A : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hcoeff : ∀ J : κ → ℕ, 0 < (∑ j, J j) →
      ‖((coeff (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ A*Z⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖((coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p) : ℝ) : UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*A)*Z⁻¹^(∑ j, I j) := by
  have he := rough_fixed_spatial_expansion p q hp
  have h := rough_box_character_translation_bound (roughSpatialDegreeIndices κ q)
    (fun J => coeff (Finsupp.equivFunOnFinite.symm J) p) (coeff 0 p) b q Z C A hZ hC hA
    (fun J hJ => ((rough_spatial_degree_indices_mem q J).mp hJ).2) hb
    (fun J hJ => hcoeff J ((rough_spatial_degree_indices_mem q J).mp hJ).1) I hI
  rw [← he] at h
  exact h

theorem rough_box_character_untranslate {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (q : ℕ) (hp : p.totalDegree ≤ q)
    (b : κ → ℤ) (Z C A : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hcoeff : ∀ J : κ → ℕ, 0 < (∑ j, J j) →
      ‖((coeff (Finsupp.equivFunOnFinite.symm J)
        (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p) : ℝ) : UnitAddCircle)‖ ≤
          A*Z⁻¹^(∑ j, J j)) (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖((coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*A)*Z⁻¹^(∑ j, I j) := by
  have h := rough_box_character_fixed_translation
    (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p) q
    ((roughMvAffineSubstitution_degree _ _ _).trans hp) (fun j => -b j) Z C A hZ hC hA
    (fun j => by simpa only [Int.cast_neg, abs_neg] using hb j) hcoeff I hI
  simp only [Int.cast_neg, rough_mv_translation_inverse] at h
  exact h

end Hindman168
