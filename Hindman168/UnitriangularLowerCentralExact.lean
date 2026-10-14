import Hindman168.UnitriangularNilpotent
import Hindman168.UnitriangularTransvectionGeneration
import Hindman168.UnitriangularTransvectionCommutator

/-! Exact equality between the actual group lower-central series and the
superdiagonal-depth subgroups. An allowed transvection is obtained as an
actual group commutator, and exact elimination generates the full subgroup. -/

namespace Hindman168
open Matrix
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

 theorem unitriangularTransvection_mem_lowerCentral (k : ℕ) (i j : Fin n)
    (hij : i < j) (hgap : i.val + (k + 1) ≤ j.val) (c : R) :
    unitriangularTransvection i j hij c ∈
      (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k := by
  induction k generalizing i j with
  | zero => trivial
  | succ k ih =>
    let r : Fin n := ⟨j.val - 1, by omega⟩
    have hir : i < r := by change i.val < j.val - 1; omega
    have hrj : r < j := by change j.val - 1 < j.val; omega
    have hgr : i.val + (k + 1) ≤ r.val := by dsimp [r]; omega
    have hm := ih i r hir hgr
    have htop : unitriangularTransvection r j hrj (1 : R) ∈
        (⊤ : Subgroup (Unitriangular n R)) := by trivial
    have hc := Subgroup.commutator_mem_commutator hm htop
    rw [unitriangularTransvection_commutator, mul_one] at hc
    exact hc

 theorem unitriangular_lowerCentral_eq_depth (k : ℕ) :
    (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k =
      unitriangularDepthSubgroup n (k + 1) R := by
  apply le_antisymm (unitriangular_lowerCentral_le_depth k)
  apply unitriangularDepth_le_of_transvections
  intro i j hij hgap c
  exact unitriangularTransvection_mem_lowerCentral k i j hij hgap c

 theorem unitriangular_nilLowerCentralFiltration_eq_depth (k : ℕ) :
    nilLowerCentralFiltration (Unitriangular n R) k = unitriangularDepthSubgroup n k R := by
  by_cases hk : k = 0
  · subst k
    exact unitriangularDepth_zero_eq_top.symm
  · have heq : k - 1 + 1 = k := by omega
    simpa only [nilLowerCentralFiltration, heq] using
      unitriangular_lowerCentral_eq_depth (n := n) (R := R) (k - 1)

 theorem unitriangularTransvection_ne_one [Nontrivial R] (i j : Fin n) (hij : i < j) :
    unitriangularTransvection i j hij (1 : R) ≠ 1 := by
  intro h
  have heq := congrArg (fun u : Unitriangular n R =>
    (u.val : Matrix (Fin n) (Fin n) R) i j) h
  simp [Matrix.transvection, Matrix.single, Matrix.one_apply_ne (ne_of_lt hij)] at heq

 theorem unitriangular_nilpotencyClass_eq [Nontrivial R] :
    Group.nilpotencyClass (Unitriangular n R) = n - 1 := by
  apply le_antisymm unitriangular_nilpotencyClass_le
  by_cases hn : 2 ≤ n
  · by_contra hclass
    have hsmall : Group.nilpotencyClass (Unitriangular n R) ≤ n - 2 := by omega
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨n - 1, by omega⟩
    have hij : i < j := by change 0 < n - 1; omega
    have hm := unitriangularTransvection_mem_lowerCentral (n - 2) i j hij
      (by dsimp [i, j]; omega) (1 : R)
    have hbot : (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries (n - 2) = ⊥ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hsmall
    rw [hbot] at hm
    exact unitriangularTransvection_ne_one i j hij (Subgroup.mem_bot.mp hm)
  · have hz : n - 1 = 0 := by omega
    rw [hz]
    exact Nat.zero_le _

end Hindman168
