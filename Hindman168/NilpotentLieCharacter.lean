import Hindman168.NilpotentLieSubalgebraSpanning
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A nonzero nilpotent Lie algebra has a nonzero linear character.
No dimension or preselected character is assumed. -/

namespace Hindman168

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem nilpotentLie_commutator_ne_top [Nontrivial L]
    (hnil : ∃ k, LieModule.lowerCentralSeries K L L k = ⊥) :
    (LieModule.lowerCentralSeries K L L 1).toSubmodule ≠ ⊤ := by
  have hb : (⊥ : LieSubalgebra K L) ≠ ⊤ := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : L)
    have hm : x ∈ (⊥ : LieSubalgebra K L) := he ▸ LieSubalgebra.mem_top x
    exact hx hm
  have h := nilpotentLieSubalgebra_sup_commutator_ne_top
    (⊥ : LieSubalgebra K L) hnil hb
  simpa using h

theorem nilpotentLie_exists_nonzero_character [Nontrivial L]
    (hnil : ∃ k, LieModule.lowerCentralSeries K L L k = ⊥) :
    ∃ f : L →ₗ[K] K, f ≠ 0 ∧
      (LieModule.lowerCentralSeries K L L 1).toSubmodule ≤ f.ker := by
  exact Submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.mpr (nilpotentLie_commutator_ne_top hnil))

theorem lieCharacter_bracket_eq_zero (f : L →ₗ[K] K)
    (hf : (LieModule.lowerCentralSeries K L L 1).toSubmodule ≤ f.ker)
    (x y : L) : f ⁅x, y⁆ = 0 := by
  apply hf
  change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries K L L (0 + 1)
  rw [LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)

end Hindman168
