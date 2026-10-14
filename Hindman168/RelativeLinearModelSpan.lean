import Hindman168.RelativeLieSubalgebra

/-! Exact original relative model is spanned by its original diagonal
layer and its original next-layer first-coordinate inclusion. -/

namespace Hindman168
variable {L : Type*} [AddCommGroup L] [Module ℝ L]

theorem relative_linear_model_diagonal_mem (A B : Submodule ℝ L) {v : L} (hv : v ∈ A) :
    (v,v) ∈ relativeLinearModel A B :=
  (relative_linear_model_mem_iff A B _).mpr ⟨hv,hv,by rw [sub_self]; exact B.zero_mem⟩

theorem relative_linear_model_first_mem (A B : Submodule ℝ L) (hBA : B ≤ A)
    {v : L} (hv : v ∈ B) : (v,0) ∈ relativeLinearModel A B :=
  (relative_linear_model_mem_iff A B _).mpr ⟨hBA hv,A.zero_mem,by simpa only [sub_zero] using hv⟩

theorem relative_linear_model_eq_span_maps (A B : Submodule ℝ L) (hBA : B ≤ A) :
    relativeLinearModel A B =
      A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) ⊔
        B.map (LinearMap.inl ℝ L L) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨_,h2,he⟩ := (relative_linear_model_mem_iff A B v).mp hv
    have hd : (v.2,v.2) ∈ A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) := ⟨v.2,h2,rfl⟩
    have hb : (v.1-v.2,0) ∈ B.map (LinearMap.inl ℝ L L) := ⟨v.1-v.2,he,rfl⟩
    have hs := (A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) ⊔
      B.map (LinearMap.inl ℝ L L)).add_mem
      ((show A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) ≤
        A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) ⊔ B.map (LinearMap.inl ℝ L L) from le_sup_left) hd)
      ((show B.map (LinearMap.inl ℝ L L) ≤
        A.map ((LinearMap.id : L →ₗ[ℝ] L).prod LinearMap.id) ⊔ B.map (LinearMap.inl ℝ L L) from le_sup_right) hb)
    have heq : (v.2,v.2)+(v.1-v.2,0) = v := by
      apply Prod.ext
      · change v.2+(v.1-v.2) = v.1
        simpa only [add_sub_assoc] using add_sub_cancel_left v.2 v.1
      · change v.2+0 = v.2
        exact add_zero _
    rwa [heq] at hs
  · apply sup_le
    · rintro v ⟨w,hw,rfl⟩
      exact relative_linear_model_diagonal_mem A B hw
    · rintro v ⟨w,hw,rfl⟩
      exact relative_linear_model_first_mem A B hBA hw

end Hindman168
