import Hindman168.RoughJointSpatialCoefficients
import Hindman168.RoughFiniteCoefficientAssembly

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

noncomputable def roughSpatialDegreeIndices (κ : Type*) [Fintype κ] (q : ℕ) :
    Finset (κ → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : κ => Finset.range (q+1))).filter
    (fun I => 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)

noncomputable def roughSpatialDegreeSupport (κ : Type*) [Fintype κ] (q : ℕ) :
    Finset (κ →₀ ℕ) := roughFiniteMultiindices (roughSpatialDegreeIndices κ q)

theorem rough_spatial_degree_indices_mem {κ : Type*} [Fintype κ] (q : ℕ) (I : κ → ℕ) :
    I ∈ roughSpatialDegreeIndices κ q ↔ 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro j
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.single_le_sum
      (fun i _ => Nat.zero_le (I i)) (Finset.mem_univ j)).trans h.2))

theorem rough_spatial_degree_support_mem {κ : Type*} [Fintype κ] (q : ℕ) (I : κ →₀ ℕ) :
    I ∈ roughSpatialDegreeSupport κ q ↔
      0 < I.sum (fun _ e => e) ∧ I.sum (fun _ e => e) ≤ q := by
  classical
  have hsum : I.sum (fun _ e => e) = ∑ j, I j := Finsupp.sum_fintype _ _ (fun _ => rfl)
  constructor
  · intro h
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp h
    have hh := (rough_spatial_degree_indices_mem q J).mp hJ
    change 0 < (Finsupp.equivFunOnFinite.symm J).sum (fun _ e => e) ∧
      (Finsupp.equivFunOnFinite.symm J).sum (fun _ e => e) ≤ q
    have hs : (Finsupp.equivFunOnFinite.symm J).sum (fun _ e => e) = ∑ j, J j := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      rfl
    simpa only [hs] using hh
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨Finsupp.equivFunOnFinite I, ?_, ?_⟩
    · apply (rough_spatial_degree_indices_mem q _).mpr
      change 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q
      simpa only [hsum] using h
    · exact Finsupp.equivFunOnFinite.symm_apply_apply I

theorem rough_spatial_degree_support_zero {κ : Type*} [Fintype κ] (q : ℕ) :
    (0 : κ →₀ ℕ) ∉ roughSpatialDegreeSupport κ q := by
  rw [rough_spatial_degree_support_mem]
  simp

theorem rough_option_right_support_fixed {κ R : Type*} [Fintype κ] [CommSemiring R]
    (p : MvPolynomial (Option κ) R) (q : ℕ) (hp : p.totalDegree ≤ q) :
    (optionEquivRight R κ p).support ⊆ insert 0 (roughSpatialDegreeSupport κ q) := by
  classical
  intro I hI
  by_cases h0 : I = 0
  · simp [h0]
  · have hd := (rough_option_right_nonzero_weighted_degree p I (mem_support_iff.mp hI)).trans hp
    have hsum : I.sum (fun _ e => e) = ∑ j, I j := Finsupp.sum_fintype _ _ (fun _ => rfl)
    have hpos : 0 < I.sum (fun _ e => e) := by
      by_contra! h
      have hz : ∑ j, I j = 0 := by omega
      have hzj : ∀ j, I j = 0 := fun j => by
        have hj := Finset.single_le_sum (fun i _ => Nat.zero_le (I i)) (Finset.mem_univ j)
        omega
      exact h0 (Finsupp.ext hzj)
    exact Finset.mem_insert_of_mem ((rough_spatial_degree_support_mem q I).mpr
      ⟨hpos, (Nat.le_add_left _ _).trans hd⟩)

end Hindman168
