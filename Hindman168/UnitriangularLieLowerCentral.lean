import Hindman168.UnitriangularLieGeneration

/-! Exact computation of the actual Lie lower central series. Elementary
brackets generate the reverse inclusion; matrix support controls the forward
inclusion. No group/Lie central-series equality is assumed. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]
local instance lowerCentralMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) := LieRing.ofAssociativeRing

 theorem unitriangularLie_lowerCentral_le_depth (k : ℕ) :
    LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k ≤
      unitriangularLieDepth n (k + 1) R := by
  induction k with
  | zero => rw [unitriangularLieDepth_one]; exact le_top
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ]
    rw [LieSubmodule.lie_le_iff]
    intro X _ Y hY
    have hd := X.property.lie (ih hY)
    change MatrixDepth (k + 1 + 1) (X.val * Y.val - Y.val * X.val)
    change MatrixDepth (1 + (k + 1)) (X.val * Y.val - Y.val * X.val) at hd
    simpa only [Nat.add_comm 1 (k + 1)] using hd

 theorem unitriangularLieSingle_mem_lowerCentral (k : ℕ) (i j : Fin n)
    (hij : i < j) (hgap : i.val + (k + 1) ≤ j.val) (c : R) :
    unitriangularLieSingle i j hij c ∈
      LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k := by
  induction k generalizing i j with
  | zero => trivial
  | succ k ih =>
    let r : Fin n := ⟨i.val + 1, by omega⟩
    have hir : i < r := by change i.val < i.val + 1; omega
    have hrj : r < j := by change i.val + 1 < j.val; omega
    have hgr : r.val + (k + 1) ≤ j.val := by dsimp [r]; omega
    have hm := ih r j hrj hgr
    have htop : unitriangularLieSingle i r hir (1 : R) ∈
        (⊤ : LieIdeal R (UnitriangularLieAlgebra n R)) := by trivial
    have hc := LieSubmodule.lie_mem_lie htop hm
    rw [unitriangularLieSingle_bracket, one_mul] at hc
    rw [LieModule.lowerCentralSeries_succ]
    exact hc

 theorem unitriangularLie_lowerCentral_eq_depth (k : ℕ) :
    LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k =
      unitriangularLieDepth n (k + 1) R := by
  apply le_antisymm (unitriangularLie_lowerCentral_le_depth k)
  change (unitriangularLieDepth n (k + 1) R : Submodule R (UnitriangularLieAlgebra n R)) ≤
    (LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k :
      Submodule R (UnitriangularLieAlgebra n R))
  apply unitriangularLieDepth_le_of_singles
  intro i j hij hgap c
  exact unitriangularLieSingle_mem_lowerCentral k i j hij hgap c

 theorem unitriangularLie_lowerCentral_terminal :
    LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) (n - 1) = ⊥ := by
  rw [unitriangularLie_lowerCentral_eq_depth]
  exact unitriangularLieDepth_terminal (by omega)

 theorem unitriangularLie_isNilpotent :
    LieModule.IsNilpotent (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) :=
  LieModule.IsNilpotent.mk (UnitriangularLieAlgebra n R) unitriangularLie_lowerCentral_terminal

instance (n : ℕ) (R : Type*) [CommRing R] :
    LieModule.IsNilpotent (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) :=
  unitriangularLie_isNilpotent

end Hindman168
