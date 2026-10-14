import Mathlib.Algebra.Group.Subgroup.Ker

namespace Hindman168

variable {G Q : Type*} [Group G] [Group Q]

theorem lattice_layer_image_eq_of_kernel_le (q : G →* Q) (Γ H : Subgroup G)
    (hker : q.ker ≤ H) : (Γ ⊓ H).map q = Γ.map q ⊓ H.map q := by
  apply le_antisymm (Subgroup.map_inf_le Γ H q)
  rintro x ⟨hxΓ, hxH⟩
  obtain ⟨a, ha, rfl⟩ := hxΓ
  obtain ⟨b, hb, he⟩ := hxH
  have hk : a*b⁻¹ ∈ q.ker := by
    change q (a*b⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have haH : a ∈ H := by
    have h := H.mul_mem (hker hk) hb
    simpa only [inv_mul_cancel_right] using h
  exact ⟨a, ⟨ha, haH⟩, rfl⟩

theorem lattice_layer_lift_exists_of_kernel_le (q : G →* Q) (Γ H : Subgroup G)
    (hker : q.ker ≤ H) (x : Q) (hxΓ : x ∈ Γ.map q) (hxH : x ∈ H.map q) :
    ∃ a : G, a ∈ Γ ∧ a ∈ H ∧ q a = x := by
  have hx : x ∈ (Γ ⊓ H).map q := by
    rw [lattice_layer_image_eq_of_kernel_le q Γ H hker]
    exact ⟨hxΓ, hxH⟩
  obtain ⟨a, ha, hqa⟩ := hx
  exact ⟨a, ha.1, ha.2, hqa⟩

end Hindman168
