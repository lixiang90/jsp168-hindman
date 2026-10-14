import Hindman168.NilLowerCentralCommutator
import Hindman168.NilUpperFaceFiltration

/-! The paper's filtration G_0=G_1=G and G_i=gamma_i(G)
is the actual mathlib lower central series with its index shifted by one. -/

namespace Hindman168
open scoped commutatorElement

variable {G : Type*} [Group G]

def nilLowerCentralFiltration (G : Type*) [Group G] (i : ℕ) : Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries (i-1)

theorem nilLowerCentralFiltration_zero : nilLowerCentralFiltration G 0 = ⊤ := rfl

theorem nilLowerCentralFiltration_one : nilLowerCentralFiltration G 1 = ⊤ := rfl

theorem nilLowerCentralFiltration_succ (i : ℕ) :
    nilLowerCentralFiltration G (i+1) = (⊤ : Subgroup G).lowerCentralSeries i := by
  simp only [nilLowerCentralFiltration, Nat.add_sub_cancel]

theorem nilLowerCentralFiltration_antitone : Antitone (nilLowerCentralFiltration G) := by
  intro i j hij
  exact (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.sub_le_sub_right hij 1)

theorem nilLowerCentralFiltration_normal (i : ℕ) : (nilLowerCentralFiltration G i).Normal := by
  dsimp [nilLowerCentralFiltration]
  infer_instance

attribute [instance] nilLowerCentralFiltration_normal

theorem nilLowerCentralFiltration_commutator_le (i j : ℕ) :
    ⁅nilLowerCentralFiltration G i, nilLowerCentralFiltration G j⁆ ≤
      nilLowerCentralFiltration G (i+j) := by
  by_cases hi : i=0
  · subst i
    simp only [nilLowerCentralFiltration_zero, zero_add]
    exact Subgroup.commutator_le_right _ _
  by_cases hj : j=0
  · subst j
    simp only [nilLowerCentralFiltration_zero, add_zero]
    exact Subgroup.commutator_le_left _ _
  have h := lowerCentralSeries_commutator_le (G := G) (i-1) (j-1)
  have he : (i-1)+(j-1)+1 = i+j-1 := by omega
  simpa only [nilLowerCentralFiltration, he] using h

theorem nilLowerCentralFiltration_conditions : CubeGroupFiltration (nilLowerCentralFiltration G) := by
  refine ⟨nilLowerCentralFiltration_antitone, ?_⟩
  intro i j g hg h hh
  exact nilLowerCentralFiltration_commutator_le i j (Subgroup.commutator_mem_commutator hg hh)

theorem nilLowerCentralFiltration_terminal [Group.IsNilpotent G]
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) : nilLowerCentralFiltration G (s+1) = ⊥ := by
  rw [nilLowerCentralFiltration_succ]
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hs

theorem nilLowerCentralFiltration_beyond_terminal [Group.IsNilpotent G]
    {s i : ℕ} (hs : Group.nilpotencyClass G ≤ s) (hi : s+1 ≤ i) :
    nilLowerCentralFiltration G i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← nilLowerCentralFiltration_terminal hs]
  exact nilLowerCentralFiltration_antitone hi

end Hindman168
