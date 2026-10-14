import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

/-! The actual relative Lie model has two vectors in A with difference
in B. Lie ideals give its genuine bracket closure. -/

namespace Hindman168
section LinearModel
variable {L : Type*} [AddCommGroup L] [Module ℝ L]

def relativeLinearModel (A B : Submodule ℝ L) : Submodule ℝ (L × L) :=
  A.prod A ⊓ B.comap (LinearMap.fst ℝ L L - LinearMap.snd ℝ L L)

theorem relative_linear_model_mem_iff (A B : Submodule ℝ L) (v : L × L) :
    v ∈ relativeLinearModel A B ↔ v.1 ∈ A ∧ v.2 ∈ A ∧ v.1-v.2 ∈ B := by
  change (v.1 ∈ A ∧ v.2 ∈ A) ∧ v.1-v.2 ∈ B ↔ _
  exact and_assoc

end LinearModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

def relativeLieSubalgebra (A B : LieIdeal ℝ L) : LieSubalgebra ℝ (L × L) where
  toSubmodule := relativeLinearModel A.toSubmodule B.toSubmodule
  lie_mem' := by
    intro x y hx hy
    obtain ⟨hx1,hx2,hxd⟩ := (relative_linear_model_mem_iff _ _ x).mp hx
    obtain ⟨hy1,hy2,hyd⟩ := (relative_linear_model_mem_iff _ _ y).mp hy
    apply (relative_linear_model_mem_iff _ _ ⁅x,y⁆).mpr
    refine ⟨A.lie_mem hy1,A.lie_mem hy2,?_⟩
    change ⁅x.1,y.1⁆-⁅x.2,y.2⁆ ∈ B
    have he : ⁅x.1,y.1⁆-⁅x.2,y.2⁆ = ⁅x.1-x.2,y.1⁆+⁅x.2,y.1-y.2⁆ := by
      rw [sub_lie,lie_sub]
      abel
    rw [he]
    have hleft : ⁅x.1-x.2,y.1⁆ ∈ B := by
      rw [← lie_skew]
      exact B.neg_mem (B.lie_mem hxd)
    exact B.add_mem hleft (B.lie_mem hyd)

theorem relative_lie_subalgebra_mem_iff (A B : LieIdeal ℝ L) (v : L × L) :
    v ∈ relativeLieSubalgebra A B ↔ v.1 ∈ A ∧ v.2 ∈ A ∧ v.1-v.2 ∈ B :=
  relative_linear_model_mem_iff _ _ v

end Hindman168
