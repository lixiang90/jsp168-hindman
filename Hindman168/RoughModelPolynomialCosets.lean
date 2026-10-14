import Hindman168.RoughIntegerSpatialModels
import Hindman168.RoughNativePolynomialCosets

namespace Hindman168
open MvPolynomial

theorem rough_joint_model_integer_eval {κ : Type*} (s : Finset (κ →₀ ℕ))
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ) (z : ℕ)
    (P : MvPolynomial κ ℤ)
    (hP : map (Int.castRingHom ℚ) P =
      roughSpatialFixedPolynomial s (M0.eval (z : ℚ)) (fun I => (M I).eval (z : ℚ)))
    (x : κ → ℤ) :
    eval (fun t : Option κ => t.elim (z : ℚ) (fun j => (x j : ℚ)))
      (roughSpatialJointPolynomial s M0 M) = (eval x P : ℚ) := by
  rw [roughSpatialJointPolynomial_eval, ← hP]
  exact (map_eval (Int.castRingHom ℚ) x P).symm

theorem rough_joint_model_integer_real_eval {κ : Type*} (s : Finset (κ →₀ ℕ))
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ) (z : ℕ)
    (P : MvPolynomial κ ℤ)
    (hP : map (Int.castRingHom ℚ) P =
      roughSpatialFixedPolynomial s (M0.eval (z : ℚ)) (fun I => (M I).eval (z : ℚ)))
    (x : κ → ℤ) :
    eval (fun t : Option κ => t.elim (z : ℝ) (fun j => (x j : ℝ)))
      (map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)) = (eval x P : ℝ) := by
  have hc := map_eval (Rat.castHom ℝ)
    (fun t : Option κ => t.elim (z : ℚ) (fun j => (x j : ℚ)))
    (roughSpatialJointPolynomial s M0 M)
  rw [rough_joint_model_integer_eval s M0 M z P hP x] at hc
  have ht : (Rat.castHom ℝ ∘ (fun t : Option κ => t.elim (z : ℚ) (fun j => (x j : ℚ)))) =
      (fun t : Option κ => t.elim (z : ℝ) (fun j => (x j : ℝ))) := by
    funext t
    cases t <;> simp only [Function.comp_apply, Option.elim_none, Option.elim_some]
    · change ((z : ℚ) : ℝ) = (z : ℝ)
      exact Rat.cast_natCast z
    · change ((x _ : ℚ) : ℝ) = (x _ : ℝ)
      exact Rat.cast_intCast _
  rw [ht] at hc
  change (((eval x P : ℤ) : ℚ) : ℝ) = _ at hc
  simpa only [Rat.cast_intCast] using hc.symm

open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_joint_model_residue_coset {κ : Type*} [Fintype κ]
    (Γ : Subgroup G) (V : E) (K : ℕ)
    (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (s : Finset (κ →₀ ℕ)) {w H q z : ℕ} {Z A : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M0 : Polynomial ℚ)
    (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I))
    (h0 : ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) (hz : z < H)
    (x y : κ → ℤ) (hxy : ∀ j, Int.ModEq (K : ℤ) (x j) (y j)) :
    let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
      (eval (fun t : Option κ => t.elim (z : ℝ) (fun j => (x j : ℝ))) m • V)) : G ⧸ Γ) =
    QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
      (eval (fun t : Option κ => t.elim (z : ℝ) (fun j => (y j : ℝ))) m • V)) := by
  obtain ⟨P, hP⟩ := rough_models_integer_spatial_polynomial s theta M0 M hmodels h0 hz
  dsimp only
  rw [rough_joint_model_integer_real_eval s M0 M z P hP x,
    rough_joint_model_integer_real_eval s M0 M z P hP y]
  exact rough_native_integer_polynomial_coset Γ V K hK P x y hxy

end Hindman168
