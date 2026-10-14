import Hindman168.UnitriangularDepthCommutator
import Hindman168.NilLowerCentralFiltration

/-! Actual algebraic nilpotence of unit upper-triangular matrix groups.
The class bound follows from the proved support filtration and the actual
mathlib group lower-central series, not from Lie-algebra nilpotence. -/

namespace Hindman168
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

 theorem unitriangular_lowerCentral_le_depth (k : ℕ) :
    (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k ≤
      unitriangularDepthSubgroup n (k + 1) R := by
  induction k with
  | zero => rw [Subgroup.lowerCentralSeries_zero, unitriangularDepth_one_eq_top]
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    have h := Subgroup.commutator_mono ih
      (le_of_eq (unitriangularDepth_one_eq_top (n := n) (R := R)).symm)
    exact h.trans (unitriangularDepth_commutator_le (k + 1) 1)

 theorem unitriangular_lowerCentral_terminal :
    (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries (n - 1) = ⊥ := by
  apply le_antisymm _ bot_le
  have h := unitriangular_lowerCentral_le_depth (n := n) (R := R) (n - 1)
  rwa [unitriangularDepth_terminal (by omega : n ≤ n - 1 + 1)] at h

 theorem unitriangular_isNilpotent : Group.IsNilpotent (Unitriangular n R) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n - 1, unitriangular_lowerCentral_terminal⟩

attribute [instance] unitriangular_isNilpotent

 theorem unitriangular_nilpotencyClass_le : Group.nilpotencyClass (Unitriangular n R) ≤ n - 1 :=
  Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp unitriangular_lowerCentral_terminal

 def unitriangularFiltration (n : ℕ) (R : Type*) [CommRing R] (k : ℕ) :
    Subgroup (Unitriangular n R) := unitriangularDepthSubgroup n k R

 theorem unitriangularFiltration_conditions : CubeGroupFiltration (unitriangularFiltration n R) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact unitriangularDepth_antitone hij
  · intro i j u hu v hv
    exact UnitriangularDepth.commutator hu hv

 theorem unitriangularFiltration_zero : unitriangularFiltration n R 0 = ⊤ :=
  unitriangularDepth_zero_eq_top

 theorem unitriangularFiltration_one : unitriangularFiltration n R 1 = ⊤ :=
  unitriangularDepth_one_eq_top

 theorem unitriangularFiltration_terminal : unitriangularFiltration n R n = ⊥ :=
  unitriangularDepth_terminal le_rfl

 theorem unitriangularFiltration_normal (k : ℕ) : (unitriangularFiltration n R k).Normal :=
  unitriangularDepth_normal k

end Hindman168
