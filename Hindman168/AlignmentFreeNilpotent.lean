import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Countable.Basic

/-! The free step-s nilpotent group used to make Alignment choices
independent of the eventual interpretation of the generators.
Mathlib's lower central series starts at the whole group at index zero. -/

namespace Hindman168

abbrev AlignmentFreeNilpotent (E : Type*) (s : ℕ) :=
  FreeGroup E ⧸ (⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s

def alignmentFreeGenerator {E : Type*} (s : ℕ) (e : E) :
    AlignmentFreeNilpotent E s :=
  QuotientGroup.mk' ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s) (FreeGroup.of e)

theorem alignmentFreeNilpotent_countable {E : Type*} [Countable E] (s : ℕ) :
    Countable (AlignmentFreeNilpotent E s) := by
  letI : Countable (FreeGroup E) := by
    unfold FreeGroup
    infer_instance
  exact (QuotientGroup.mk'_surjective
    ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s)).countable

theorem alignmentFreeNilpotent_lowerCentralSeries (E : Type*) (s : ℕ) :
    (⊤ : Subgroup (AlignmentFreeNilpotent E s)).lowerCentralSeries s = ⊥ := by
  let N := (⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s
  have htop : (⊤ : Subgroup (FreeGroup E)).map (QuotientGroup.mk' N) = ⊤ := by
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  rw [← htop, ← Subgroup.map_lowerCentralSeries]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']

theorem alignmentFreeLift_kills_series {E G : Type*} [Group G]
    (s : ℕ) (L : E → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s ≤ (FreeGroup.lift L).ker := by
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [Subgroup.map_lowerCentralSeries]
  apply le_bot_iff.mp
  rw [← hG]
  exact Subgroup.lowerCentralSeries_mono s le_top

def alignmentFreeInterpretation {E G : Type*} [Group G]
    (s : ℕ) (L : E → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    AlignmentFreeNilpotent E s →* G :=
  QuotientGroup.lift ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s)
    (FreeGroup.lift L) (alignmentFreeLift_kills_series s L hG)

theorem alignmentFreeInterpretation_generator {E G : Type*} [Group G]
    (s : ℕ) (L : E → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (e : E) :
    alignmentFreeInterpretation s L hG (alignmentFreeGenerator s e) = L e := by
  exact (QuotientGroup.lift_mk' ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s)
    (alignmentFreeLift_kills_series s L hG)
    (FreeGroup.of e)).trans FreeGroup.lift_apply_of

end Hindman168
