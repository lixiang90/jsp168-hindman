import Hindman168.RoughJointHorizontalError
import Hindman168.RoughNativeKernelLogPolynomial

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff

variable {κ E : Type*} [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_horizontal_model_kernel
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ v ∈ nativeLieSubalgebraModel S, ∀ w ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) v w) = 0)
    (V : E) (hV : V ∈ nativeLieSubalgebraModel S) (hFV : F V = 1)
    (s : Finset (κ →₀ ℕ)) {w H q : ℕ} {Z A : ℝ}
    (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ J ∈ s, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J))
    (hM0 : M0.natDegree ≤ q) (he : ∀ J ∈ s, (∑ j, J j) ≤ q)
    (hP0 : P0.natDegree ≤ q)
    (htheta : ∀ J ∈ s, (theta J).natDegree + J.sum (fun _ e => e) ≤ q)
    (p : RoughVectorMvPolynomial (Option κ) E) (P : (Option κ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (hd : RoughVectorMvDegreeLE p q)
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hchi : ∀ x, nativeLieLogarithmCharacter (I := I) (G := G) F (P x) =
      eval x (roughSpatialJointPolynomial s P0 theta)) :
    let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)
    let a := roughSpatialJointPolynomial s P0 theta - m
    ∃ Q : RoughVectorMvPolynomial (Option κ) E,
      RoughVectorMvDegreeLE Q
        ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
          (Group.nilpotencyClass G + 1)) ^ 2) * q) ∧
      (∀ x, roughVectorMvEval Q x = nativeLieGlobalLogarithm (E := E) (I := I)
        (roughNativeKernelFactor (I := I) V (eval x a) (eval x m) (P x))) ∧
      (∀ x, roughVectorMvEval Q x ∈ nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF)) := by
  let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)
  let a := roughSpatialJointPolynomial s P0 theta - m
  have hm : m.totalDegree ≤ q := rough_models_joint_real_degree s theta M0 M hmodels hM0 he
  have hn : (-m).totalDegree ≤ q := by
    rw [← neg_one_smul ℝ m]
    exact (totalDegree_smul_le (-1 : ℝ) m).trans hm
  have ha : a.totalDegree ≤ q := by
    dsimp only [a]
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans
      (max_le (roughSpatialJointPolynomial_degree s P0 theta q hP0 htheta) hn)
  have hc : ∀ x, nativeLieLogarithmCharacter (I := I) (G := G) F (P x) =
      eval x a + eval x m := by
    intro x
    rw [hchi x]
    change _ = eval x (roughSpatialJointPolynomial s P0 theta - m) + eval x m
    rw [map_sub, sub_add_cancel]
  refine ⟨roughNativeKernelLogPolynomial (I := I) (G := G) V a m p,
    roughNativeKernelLogPolynomial_degree V a m ha hm hd,
    roughNativeKernelLogPolynomial_eval V a m p P hp, ?_⟩
  exact roughNativeKernelLogPolynomial_mem S F hF V hV hFV a m p P hp hP hc

end Hindman168
