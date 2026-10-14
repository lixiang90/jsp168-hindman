import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

/-! Actual diagonal subspace of a specified original real layer. -/

namespace Hindman168
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def diagonalLinearModel (A : Submodule ℝ E) : Submodule ℝ (E × E) :=
  A.map ((LinearMap.id : E →ₗ[ℝ] E).prod LinearMap.id)

theorem diagonal_linear_model_mem_iff (A : Submodule ℝ E) (v : E × E) :
    v ∈ diagonalLinearModel A ↔ v.1 ∈ A ∧ v.1=v.2 := by
  constructor
  · rintro ⟨w,hw,hv⟩
    change (w,w)=v at hv
    cases hv
    exact ⟨hw,rfl⟩
  · rintro ⟨h1,he⟩
    exact ⟨v.1,h1,Prod.ext rfl he⟩

theorem diagonal_linear_model_diagonal_mem (A : Submodule ℝ E) {v : E} (hv : v ∈ A) :
    (v,v) ∈ diagonalLinearModel A := ⟨v,hv,rfl⟩

end Hindman168
