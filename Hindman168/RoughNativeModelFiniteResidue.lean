import Hindman168.RoughModelPolynomialCosets
import Hindman168.RoughBoxPartition

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_joint_model_finite_residue {κ : Type*} [Fintype κ]
    (Γ : Subgroup G) (V : E) (K : ℕ) (hK : 0 < K)
    (hperiod : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (support : Finset (κ →₀ ℕ)) {w H q z : ℕ} {Z A : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M0 : Polynomial ℚ)
    (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J))
    (h0 : ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) (hz : z < H) (u : κ → ℤ) :
    ∃ j : Fin K, ∀ x : κ → ℤ, (∀ k, Int.ModEq (K : ℤ) (x k) (u k)) →
      (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
        (MvPolynomial.eval (Option.elim · (z : ℝ) (fun k => (x k : ℝ)))
          (MvPolynomial.map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G) (((j.val : ℤ) : ℝ) • V)) := by
  obtain ⟨P, hP⟩ := rough_models_integer_spatial_polynomial support theta M0 M hmodels h0 hz
  let j := roughResidueLabel K hK (MvPolynomial.eval u P)
  refine ⟨j, ?_⟩
  intro x hx
  rw [rough_joint_model_integer_real_eval support M0 M z P hP x]
  apply rough_native_exponential_modEq Γ V K hperiod
  exact (rough_integer_polynomial_modEq P (K : ℤ) x u hx).trans
    ((rough_residue_label_iff K hK (MvPolynomial.eval u P) j).mp rfl)

end Hindman168
