import Hindman168.AlignmentPolynomialArrayGroup

/-! Every actual pointwise array subgroup inherits the original fixed
lower-central cutoff. No new or enlarged nilpotency step is assumed. -/

namespace Hindman168

theorem pointwiseArraySubgroup_lowerCentral_bot {Z G : Type*} [Group G]
    (A : Subgroup (Z → G)) (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup A).lowerCentralSeries s = ⊥ := by
  apply le_bot_iff.mp
  intro a ha
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  funext z
  let ev : A →* G := { toFun := fun b => b.val z, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hle : ((⊤ : Subgroup A).lowerCentralSeries s).map ev ≤
      (⊤ : Subgroup G).lowerCentralSeries s := by
    rw [Subgroup.map_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono s le_top
  have h := hle (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  rw [hG] at h
  exact Subgroup.mem_bot.mp h

theorem pointwiseArraySubgroup_nilpotent {Z G : Type*} [Group G]
    (A : Subgroup (Z → G)) (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Group.IsNilpotent A :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨s, pointwiseArraySubgroup_lowerCentral_bot A s hG⟩

theorem pointwiseArraySubgroup_nilpotencyClass_le {Z G : Type*} [Group G]
    (A : Subgroup (Z → G)) (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Group.nilpotencyClass A ≤ s := by
  letI := pointwiseArraySubgroup_nilpotent A s hG
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (pointwiseArraySubgroup_lowerCentral_bot A s hG)

end Hindman168
