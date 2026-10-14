import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The strong commutator law for the actual lower central series.
The three-subgroup inclusion is proved by passing to the normal quotient. -/

namespace Hindman168
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem normal_threeSubgroup_commutator_le
    (A B C K : Subgroup G) [K.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ K) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ K) : ⁅⁅A, B⁆, C⁆ ≤ K := by
  let f := QuotientGroup.mk' K
  have hz (H : Subgroup G) : H.map f = ⊥ ↔ H ≤ K := by
    rw [Subgroup.map_eq_bot_iff]
    simp only [f, QuotientGroup.ker_mk']
  apply (hz _).mp
  have hm₁ := (hz _).mpr h₁
  have hm₂ := (hz _).mpr h₂
  simp only [Subgroup.map_commutator] at hm₁ hm₂ ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate hm₁ hm₂

theorem lowerCentralSeries_commutator_le (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i+j+1) := by
  induction i generalizing j with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero, Subgroup.commutator_comm,
      ← Subgroup.lowerCentralSeries_succ]
    simpa only [zero_add] using (le_refl ((⊤ : Subgroup G).lowerCentralSeries (j+1)))
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply normal_threeSubgroup_commutator_le
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G), ← Subgroup.lowerCentralSeries_succ,
        Subgroup.commutator_comm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j+1)
    · have hc : ⁅(⊤ : Subgroup G).lowerCentralSeries j,
          (⊤ : Subgroup G).lowerCentralSeries i⁆ ≤
          (⊤ : Subgroup G).lowerCentralSeries (i+j+1) := by
        rw [Subgroup.commutator_comm]
        exact ih j
      have h := Subgroup.commutator_mono hc (le_refl (⊤ : Subgroup G))
      rw [← Subgroup.lowerCentralSeries_succ] at h
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Hindman168
