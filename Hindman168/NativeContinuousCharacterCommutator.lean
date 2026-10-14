import Hindman168.NativeFilteredHorizontalCoordinates

namespace Hindman168
open scoped Manifold ContDiff commutatorElement

variable {G : Type*} [Group G]

theorem native_additive_character_one (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) : χ 1 = 0 := by
  have h := hmul 1 1
  rw [one_mul] at h
  linarith

theorem native_additive_character_inv (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (g : G) : χ g⁻¹ = -χ g := by
  have h := hmul g g⁻¹
  rw [mul_inv_cancel, native_additive_character_one χ hmul] at h
  linarith

theorem native_additive_character_commutator (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h)
    (g : G) (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : χ g = 0 := by
  let q : G →* Multiplicative ℝ :=
    { toFun := fun x => Multiplicative.ofAdd (χ x)
      map_one' := native_additive_character_one χ hmul
      map_mul' := hmul }
  have hk : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ q.ker := by
    rw [Subgroup.top_lowerCentralSeries_one, commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change q ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact hk hg

end Hindman168
