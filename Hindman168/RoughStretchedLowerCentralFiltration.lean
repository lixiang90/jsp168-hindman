import Hindman168.RoughStretchedFiltrationIndices
import Hindman168.NilLowerCentralFiltration

/-! The stretched filtration uses the actual group lower central series.
The positive stretch D is fixed before the polynomial and its translations. -/

namespace Hindman168
open scoped commutatorElement

variable {G : Type*} [Group G]

def roughStretchedLowerCentralFiltration (G : Type*) [Group G] (D i : ℕ) : Subgroup G :=
  nilLowerCentralFiltration G (i ⌈/⌉ D)

theorem rough_stretched_filtration_zero (D : ℕ) :
    roughStretchedLowerCentralFiltration G D 0 = ⊤ := by
  simp only [roughStretchedLowerCentralFiltration, zero_ceilDiv,
    nilLowerCentralFiltration_zero]

theorem rough_stretched_filtration_one (D : ℕ) (hD : 0 < D) :
    roughStretchedLowerCentralFiltration G D 1 = ⊤ := by
  rw [roughStretchedLowerCentralFiltration, rough_ceiling_index_one D hD,
    nilLowerCentralFiltration_one]

theorem rough_stretched_filtration_initial (D : ℕ) (hD : 0 < D)
    (i : ℕ) (hi : i ≤ D) : roughStretchedLowerCentralFiltration G D i = ⊤ := by
  have h := rough_ceiling_index_initial D hD i hi
  have he : (i ⌈/⌉ D)-1 = 0 := by omega
  simp only [roughStretchedLowerCentralFiltration, nilLowerCentralFiltration, he,
    Subgroup.lowerCentralSeries_zero]

theorem rough_stretched_filtration_antitone (D : ℕ) (hD : 0 < D) :
    Antitone (roughStretchedLowerCentralFiltration G D) := by
  intro i j hij
  exact nilLowerCentralFiltration_antitone (rough_ceiling_index_monotone D hD hij)

theorem rough_stretched_filtration_normal (D i : ℕ) :
    (roughStretchedLowerCentralFiltration G D i).Normal :=
  nilLowerCentralFiltration_normal (i ⌈/⌉ D)

theorem rough_stretched_filtration_commutator_le (D : ℕ) (hD : 0 < D) (i j : ℕ) :
    ⁅roughStretchedLowerCentralFiltration G D i,
      roughStretchedLowerCentralFiltration G D j⁆ ≤
      roughStretchedLowerCentralFiltration G D (i+j) := by
  exact le_trans (nilLowerCentralFiltration_commutator_le _ _)
    (nilLowerCentralFiltration_antitone (rough_ceiling_index_add D hD i j))

theorem rough_stretched_filtration_conditions (D : ℕ) (hD : 0 < D) :
    CubeGroupFiltration (roughStretchedLowerCentralFiltration G D) := by
  refine ⟨rough_stretched_filtration_antitone D hD, ?_⟩
  intro i j g hg h hh
  exact rough_stretched_filtration_commutator_le D hD i j
    (Subgroup.commutator_mem_commutator hg hh)

theorem rough_stretched_filtration_terminal [Group.IsNilpotent G]
    (D : ℕ) (hD : 0 < D) {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) :
    roughStretchedLowerCentralFiltration G D (s*D+1) = ⊥ := by
  exact nilLowerCentralFiltration_beyond_terminal hs (rough_ceiling_index_terminal D hD s)

theorem rough_stretched_filtration_beyond_terminal [Group.IsNilpotent G]
    (D : ℕ) (hD : 0 < D) {s i : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hi : s*D+1 ≤ i) : roughStretchedLowerCentralFiltration G D i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← rough_stretched_filtration_terminal D hD hs]
  exact rough_stretched_filtration_antitone D hD hi

end Hindman168
