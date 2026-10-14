import Hindman168.NativeSubgroupHorizontalEscape
import Hindman168.RoughAffineCommonMultiplier
import Hindman168.RoughVectorSpatialAffineProjection

/-! Arbitrary translations leave the actual highest scalar coefficient
unchanged; a fixed dilation multiplies it by its degree power. All scalar
coefficients are those of the original adapted source. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_horizontal_projection_totalDegree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ) (j : ℕ) (hNext : F.layer (j+1) ≤ phi.ker)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    (roughVectorMvProjection phi p).totalDegree ≤ j := by
  apply Finset.sup_le
  intro J hJ
  by_contra hbad
  have hm := rough_vector_weighted_coefficient F.layer F.antitone hp J
  simp only [Nat.add_zero] at hm
  have hz := hNext (F.antitone (by omega) hm)
  have he : MvPolynomial.coeff J (roughVectorMvProjection phi p) = 0 := by
    rw [← rough_vector_coefficient_projection]
    exact hz
  exact (MvPolynomial.mem_support_iff.mp hJ) he

theorem native_subgroup_affine_top_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (j : ℕ) (hNext : F.layer (j+1) ≤ phi.ker)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b d : ℝ) :
    MvPolynomial.coeff (Finsupp.single () j) (roughVectorMvProjection phi
      (roughVectorMvAffineSubstitution (fun _ => b) (fun _ => d) p)) =
      d^j * (phi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) /
        (j.factorial : ℝ)) := by
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Unit => j) = Finsupp.single () j := by
    apply Finsupp.ext
    intro x
    cases x
    simp
  rw [rough_vector_projection_affine_substitution, ← he, rough_affine_uniform_coefficient]
  rw [he, rough_translation_top_coefficient (fun _ => b) _ _
    (by simpa using native_subgroup_horizontal_projection_totalDegree D F phi j hNext p hp)]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [native_subgroup_taylor_top_coefficient D F phi hB j hNext p hp]

end Hindman168
