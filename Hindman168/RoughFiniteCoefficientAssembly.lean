import Hindman168.RoughIntegerSpatialModels

namespace Hindman168
open MvPolynomial

theorem rough_mv_coefficient_map_degree {κ R T : Type*} [CommSemiring R] [CommSemiring T]
    (f : R →+* T) (P : MvPolynomial κ R) : (map f P).totalDegree ≤ P.totalDegree :=
  Finset.sup_mono (support_map_subset f P)

theorem rough_models_joint_real_degree {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) {w H q : ℕ} {Z A : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M0 : Polynomial ℚ)
    (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I))
    (h0 : M0.natDegree ≤ q) (he : ∀ I ∈ s, (∑ j, I j) ≤ q) :
    (map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)).totalDegree ≤ q := by
  apply (rough_mv_coefficient_map_degree _ _).trans
  apply roughSpatialJointPolynomial_degree s M0 M q h0
  intro I hI
  have hd := (hmodels I hI).1
  have hsum : I.sum (fun _ e => e) = ∑ j, I j := by
    exact Finsupp.sum_fintype _ _ (fun _ => rfl)
  rw [hsum]
  exact (Nat.add_le_add_right hd _).trans (by rw [Nat.sub_add_cancel (he I hI)])

noncomputable def roughFiniteMultiindices {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) : Finset (κ →₀ ℕ) :=
  s.map Finsupp.equivFunOnFinite.symm.toEmbedding

theorem roughFiniteMultiindices_models {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) {w H q : ℕ} {Z A : ℝ}
    (theta : (κ → ℕ) → Polynomial ℝ) (M : (κ → ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I)) :
    ∀ I ∈ roughFiniteMultiindices s,
      RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I) := by
  intro I hi
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hi
  exact hmodels J hJ

theorem roughFiniteMultiindices_degree {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (q : ℕ) (he : ∀ I ∈ s, (∑ j, I j) ≤ q) :
    ∀ I ∈ roughFiniteMultiindices s, (∑ j, I j) ≤ q := by
  intro I hi
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hi
  exact he J hJ

end Hindman168
