import Hindman168.CurveSuperpositionDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual bounded pointwise operator associated with a continuous
curve of continuous linear maps. The original supremum norms give all
operator bounds; no derivative operator on curve space is assumed. -/

namespace Hindman168
open Set Topology
open scoped ContDiff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

 noncomputable def curveApplyLinear (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) := by
  let T : C(K, E) →ₗ[ℝ] C(K, F) :=
    { toFun := fun α => ⟨fun t => A t (α t), A.continuous.clm_apply α.continuous⟩
      map_add' := fun α β => by ext t; exact map_add (A t) (α t) (β t)
      map_smul' := fun c α => by ext t; exact (A t).map_smul c (α t) }
  exact T.mkContinuous ‖A‖ (fun α => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg α))).mpr
      intro t
      exact ((A t).le_opNorm (α t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (α.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _)))

 theorem curveApplyLinear_apply (A : C(K, E →L[ℝ] F)) (α : C(K, E)) (t : K) :
    curveApplyLinear A α t = A t (α t) := rfl

 theorem curveApplyLinear_norm_le (A : C(K, E →L[ℝ] F)) : ‖curveApplyLinear A‖ ≤ ‖A‖ := by
  apply (curveApplyLinear A).opNorm_le_bound (norm_nonneg A)
  intro α
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg α))).mpr
  intro t
  exact ((A t).le_opNorm (α t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (α.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

 noncomputable def curvePointwiseOperator : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) := by
  let T : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
    { toFun := curveApplyLinear (K := K) (E := E) (F := F)
      map_add' := fun A B => by ext α t; rfl
      map_smul' := fun c A => by ext α t; rfl }
  exact T.mkContinuous 1 (fun A : C(K, E →L[ℝ] F) => by
    simp only [one_mul]
    convert! curveApplyLinear_norm_le (K := K) (E := E) (F := F) A using 1)

 theorem curvePointwiseOperator_apply (A : C(K, E →L[ℝ] F)) (α : C(K, E)) (t : K) :
    curvePointwiseOperator A α t = A t (α t) := rfl

 theorem curvePointwiseOperator_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (curvePointwiseOperator (K := K) (E := E) (F := F)) :=
  ContinuousLinearMap.contDiff _

 theorem curveApplyLinear_const (L : E →L[ℝ] F) :
    curveApplyLinear (ContinuousMap.const K L) = ContinuousLinearMap.compLeftContinuous ℝ K L := by
  ext α t
  rfl

end Hindman168
