import Hindman168.NativeLieExponentialSmooth
import Hindman168.LieExponentialHomomorphism
import Mathlib.Algebra.Group.End

/-! The native adjoint is the genuine derivative of original group
conjugation. Its representation and inverse laws follow from the actual
group identities and the native manifold chain rule. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieConjugation_contMDiff (g : G) :
    ContMDiff I I ∞ (fun x : G => g * x * g⁻¹) := by
  have hl : ContMDiff I I ∞ (fun x : G => g * x) := contMDiff_mul_left
  have hr : ContMDiff I I ∞ (fun x : G => x * g⁻¹) := contMDiff_mul_right
  exact hr.comp hl

 theorem nativeLieConjugation_joint_contMDiff :
    ContMDiff (I.prod I) I ∞ (fun p : G × G => p.1 * p.2 * p.1⁻¹) := by
  have hm : ContMDiff (I.prod I) I ∞ (fun p : G × G => p.1 * p.2) := contMDiff_mul I ∞
  have hi : ContMDiff (I.prod I) I ∞ (fun p : G × G => p.1⁻¹) := contMDiff_fst.inv
  convert! hm.mul hi using 1

 noncomputable def nativeLieAdjoint (g : G) : E →L[ℝ] E :=
  mfderiv I I (fun x : G => g * x * g⁻¹) (1 : G)

omit [LieGroup I ∞ G] in
 theorem nativeLieAdjoint_apply (g : G) (v : E) :
    nativeLieAdjoint (I := I) g v =
      mfderiv I I (fun x : G => g * x * g⁻¹) (1 : G) v := rfl

omit [LieGroup I ∞ G] in
 theorem nativeLieAdjoint_one :
    nativeLieAdjoint (I := I) (1 : G) = ContinuousLinearMap.id ℝ E := by
  unfold nativeLieAdjoint
  have heq : (fun x : G => (1 : G) * x * (1 : G)⁻¹) = id := by ext x; simp
  rw [heq, mfderiv_id]
  rfl

 theorem nativeLieAdjoint_mul (g h : G) :
    nativeLieAdjoint (I := I) (g * h) =
      (nativeLieAdjoint (I := I) g).comp (nativeLieAdjoint (I := I) h) := by
  have heq : (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) =
      (fun x : G => (g * h) * x * (g * h)⁻¹) := by ext x; simp only [comp_apply]; group
  apply ContinuousLinearMap.ext
  intro v
  have hd := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I)
    (1 : G) ((nativeLieConjugation_contMDiff (I := I) g).mdifferentiableAt (by norm_num))
    ((nativeLieConjugation_contMDiff (I := I) h).mdifferentiableAt (by norm_num))
    (by simp : h * (1 : G) * h⁻¹ = 1) v
  rw [heq] at hd
  exact hd

 theorem nativeLieAdjoint_inv_comp (g : G) :
    (nativeLieAdjoint (I := I) g⁻¹).comp (nativeLieAdjoint (I := I) g) =
      ContinuousLinearMap.id ℝ E := by
  rw [← nativeLieAdjoint_mul, inv_mul_cancel, nativeLieAdjoint_one]

 theorem nativeLieAdjoint_comp_inv (g : G) :
    (nativeLieAdjoint (I := I) g).comp (nativeLieAdjoint (I := I) g⁻¹) =
      ContinuousLinearMap.id ℝ E := by
  rw [← nativeLieAdjoint_mul, mul_inv_cancel, nativeLieAdjoint_one]

 theorem nativeLieAdjoint_inv_apply (g : G) (v : E) :
    nativeLieAdjoint (I := I) g⁻¹ (nativeLieAdjoint (I := I) g v) = v := by
  have h := congrArg (fun L : E →L[ℝ] E => L v) (nativeLieAdjoint_inv_comp (I := I) g)
  exact h

 theorem nativeLieAdjoint_apply_inv (g : G) (v : E) :
    nativeLieAdjoint (I := I) g (nativeLieAdjoint (I := I) g⁻¹ v) = v := by
  have h := congrArg (fun L : E →L[ℝ] E => L v) (nativeLieAdjoint_comp_inv (I := I) g)
  exact h

 theorem nativeLieAdjoint_injective (g : G) :
    Injective (nativeLieAdjoint (I := I) g) :=
  Function.LeftInverse.injective (nativeLieAdjoint_inv_apply (I := I) g)

 theorem nativeLieAdjoint_surjective (g : G) :
    Surjective (nativeLieAdjoint (I := I) g) :=
  Function.RightInverse.surjective (nativeLieAdjoint_apply_inv (I := I) g)

end Hindman168
