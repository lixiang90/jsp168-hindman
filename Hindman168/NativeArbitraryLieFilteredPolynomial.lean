import Hindman168.NativeNilmanifoldData
import Hindman168.RoughNativePolynomialFiltered

/-! Actual native group-difference polynomials work for ANY actual Lie
model filtration with proved bracket/antitone/exponential-layer inputs.
Applications discharge those inputs from the original relative native data. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_arbitrary_lie_group_difference_weighted {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (h : σ → ℝ) {p : RoughVectorMvPolynomial σ D.E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughNativeGroupDifferenceMvPolynomial (I := D.I) (G := D.G) h p) (k+1) := by
  apply rough_parametric_weighted_endpoint
  apply rough_parametric_picard_perturbation_weighted _ hF _ hB
  · exact rough_vector_weighted_scale _ _ hp
  · exact rough_vector_weighted_scale _ _ hp
  · exact hp
  · exact rough_vector_weighted_affine _ hF _ _ hp
  · intro a ha; exact False.elim (List.not_mem_nil ha)
  · exact rough_vector_weighted_difference _ hF _ hp

theorem native_arbitrary_lie_iterated_difference_weighted {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    {p : RoughVectorMvPolynomial σ D.E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) (hs : List (σ → ℝ)) :
    RoughVectorMvWeightedDegree F (roughNativeIteratedDifferenceMvPolynomial (I := D.I) (G := D.G) p hs)
      (k+hs.length) := by
  induction hs with
  | nil => exact hp
  | cons h hs ih =>
      simpa only [roughNativeIteratedDifferenceMvPolynomial,List.length_cons,Nat.add_assoc] using
        native_arbitrary_lie_group_difference_weighted D F hF hB h ih

theorem native_arbitrary_lie_polynomial_filtered {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (L : ℕ → Subgroup D.G)
    (hExp : ∀ i v, v ∈ F i → nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈ L i)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F p 0) :
    RoughFilteredPolynomial L (fun x : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p x)) := by
  intro hs x
  have hw := native_arbitrary_lie_iterated_difference_weighted D F hF hB hp hs
  have hm := hExp (0+hs.length) _ (rough_vector_weighted_eval F hF hw x)
  have he := rough_native_iterated_difference_polynomial_eval (E := D.E) (I := D.I) (G := D.G) p hs x
  have hg := congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)) he
  rw [nativeLieExponential_globalLogarithm] at hg
  rw [hg] at hm
  simpa only [Nat.zero_add] using hm

end Hindman168
