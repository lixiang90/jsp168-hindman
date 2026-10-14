import Hindman168.RoughJointCoefficientPolynomial
import Hindman168.RoughDescentModels

namespace Hindman168
open MvPolynomial

theorem roughSpatialFixedPolynomial_map {κ R T : Type*} [CommSemiring R] [CommSemiring T]
    (f : R →+* T) (s : Finset (κ →₀ ℕ)) (a0 : R) (a : (κ →₀ ℕ) → R) :
    map f (roughSpatialFixedPolynomial s a0 a) =
      roughSpatialFixedPolynomial s (f a0) (fun I => f (a I)) := by
  simp only [roughSpatialFixedPolynomial, map_add, map_sum, map_C, map_monomial]

theorem roughSpatialFixedPolynomial_integer {κ : Type*} (s : Finset (κ →₀ ℕ))
    (a0 : ℚ) (a : (κ →₀ ℕ) → ℚ)
    (h0 : ∃ n : ℤ, a0 = (n : ℚ)) (ha : ∀ I ∈ s, ∃ n : ℤ, a I = (n : ℚ)) :
    ∃ P : MvPolynomial κ ℤ,
      map (Int.castRingHom ℚ) P = roughSpatialFixedPolynomial s a0 a := by
  classical
  obtain ⟨n0, hn0⟩ := h0
  have hall : ∀ I, ∃ n : ℤ, I ∈ s → a I = (n : ℚ) := by
    intro I
    by_cases hi : I ∈ s
    · obtain ⟨n, hn⟩ := ha I hi
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose n hn using hall
  refine ⟨roughSpatialFixedPolynomial s n0 n, ?_⟩
  rw [roughSpatialFixedPolynomial_map]
  unfold roughSpatialFixedPolynomial
  change C (n0 : ℚ) + ∑ I ∈ s, monomial I (n I : ℚ) = _
  rw [← hn0]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [hn I hi]

theorem rough_models_integer_spatial_polynomial {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) {w H q z : ℕ} {Z A : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M0 : Polynomial ℚ)
    (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I))
    (h0 : ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) (hz : z < H) :
    ∃ P : MvPolynomial κ ℤ,
      map (Int.castRingHom ℚ) P =
        roughSpatialFixedPolynomial s (M0.eval (z : ℚ)) (fun I => (M I).eval (z : ℚ)) :=
  roughSpatialFixedPolynomial_integer s _ _ h0
    (fun I hI => ((hmodels I hI).2.2 z hz).1)

end Hindman168
