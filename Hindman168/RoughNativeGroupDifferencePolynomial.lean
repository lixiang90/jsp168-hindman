import Hindman168.RoughParametricPicardPerturbation
import Hindman168.RoughNativeProductMvPolynomial
import Hindman168.RoughWeightedPolynomialDifference
import Hindman168.RoughNativeWeightedPolynomial

namespace Hindman168
open scoped Manifold ContDiff

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeGroupDifferenceMvPolynomial (h : κ → ℝ)
    (p : RoughVectorMvPolynomial κ E) : RoughVectorMvPolynomial κ E :=
  roughParametricEndpoint (roughParametricPicardPerturbation
    (nativeLieAdjointDifferential (I := I) (G := G)) (Group.nilpotencyClass G)
    (roughVectorMvScale (-1) p) (roughVectorMvScale (-1) p) [] p
    (roughVectorMvAffineSubstitution h (fun _ => 1) p) (roughVectorMvDifference h p)
    (Group.nilpotencyClass G+1))

omit [Fintype κ] in
theorem rough_native_group_difference_polynomial_eval (h x : κ → ℝ)
    (p : RoughVectorMvPolynomial κ E) :
    roughVectorMvEval (E := E) (roughNativeGroupDifferenceMvPolynomial (I := I) (G := G) h p) x =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p (x+h)) *
          (nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p x))⁻¹) := by
  have hw : ∀ y, roughVectorMvEval ([] : RoughVectorMvPolynomial κ E) y =
      roughVectorMvEval (roughVectorMvScale (-1) p) y-
        roughVectorMvEval (roughVectorMvScale (-1) p) y := by
    intro y
    simp only [roughVectorMvEval, List.map_nil, List.sum_nil, sub_self]
  have hu : ∀ y, roughVectorMvEval (roughVectorMvDifference h p) y =
      roughVectorMvEval (roughVectorMvAffineSubstitution h (fun _ => 1) p) y-roughVectorMvEval p y := by
    intro y
    rw [rough_vector_difference_eval, roughVectorMvAffineSubstitution_eval]
    simp only [one_mul, add_comm]
  have ht := rough_parametric_picard_perturbation_eval
    (nativeLieAdjointDifferential (I := I) (G := G)) (Group.nilpotencyClass G)
    (roughVectorMvScale (-1) p) (roughVectorMvScale (-1) p) [] p
    (roughVectorMvAffineSubstitution h (fun _ => 1) p) (roughVectorMvDifference h p)
    hw hu (Group.nilpotencyClass G+1) x 1
  simp only [← rough_parametric_eval_endpoint] at ht
  change roughVectorMvEval (E := E)
      (roughNativeGroupDifferenceMvPolynomial (I := I) (G := G) h p) x =
    roughVectorMvEval (E := E) (roughNativeProductMvPolynomial (I := I) (G := G)
      (roughVectorMvAffineSubstitution h (fun _ => 1) p) (roughVectorMvScale (-1) p)) x-
    roughVectorMvEval (E := E) (roughNativeProductMvPolynomial (I := I) (G := G)
      p (roughVectorMvScale (-1) p)) x at ht
  rw [roughNativeProductMvPolynomial_eval, roughNativeProductMvPolynomial_eval,
    roughVectorMvEval_scale, neg_one_smul, roughVectorMvAffineSubstitution_eval] at ht
  have hn : nativeLieExponential (I := I) (G := G) (-roughVectorMvEval (E := E) p x) =
      (nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p x))⁻¹ :=
    nativeLieExponential_neg (I := I) (G := G) (roughVectorMvEval (E := E) p x)
  rw [hn, mul_inv_cancel, nativeLieGlobalLogarithm_one, sub_zero] at ht
  convert ht using 1
  congr 3
  apply congrArg (roughVectorMvEval (E := E) p)
  funext j
  simp only [one_mul, Pi.add_apply, add_comm]

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem rough_native_group_difference_polynomial_weighted (D : ℕ) (hD : 0 < D)
    (h : κ → ℝ) {p : RoughVectorMvPolynomial κ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) p k) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D)
      (roughNativeGroupDifferenceMvPolynomial (I := I) (G := G) h p) (k+1) := by
  apply rough_parametric_weighted_endpoint
  apply rough_parametric_picard_perturbation_weighted _
    (rough_native_stretched_lie_antitone D hD) _
    (fun i j v w hv hw => rough_native_stretched_lie_bracket D hD hv hw)
  · exact rough_vector_weighted_scale _ _ hp
  · exact rough_vector_weighted_scale _ _ hp
  · exact hp
  · exact rough_vector_weighted_affine _ (rough_native_stretched_lie_antitone D hD) _ _ hp
  · intro a ha
    exact False.elim (List.not_mem_nil ha)
  · exact rough_vector_weighted_difference _ (rough_native_stretched_lie_antitone D hD) _ hp

end Hindman168
