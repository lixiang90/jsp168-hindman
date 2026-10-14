import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic

/-! Exact Bezout combination of the multiple subgroups used by the
subgroup inverse argument. -/
namespace Hindman168

def multipleAddSubgroup (G : Type*) [AddCommGroup G] (q : ℕ) : AddSubgroup G :=
  (show G →+ G from {
    toFun := fun x => q • x
    map_zero' := smul_zero q
    map_add' := fun x y => nsmul_add x y q }).range

theorem mem_multipleAddSubgroup (G : Type*) [AddCommGroup G] (q : ℕ) (x : G) :
    x ∈ multipleAddSubgroup G q ↔ ∃ y : G, q • y = x := Iff.rfl

theorem coprime_multiple_decomposition {G : Type*} [AddCommGroup G]
    (a b : ℕ) (hc : a.Coprime b) (x : G) :
    ∃ y z : G, a • y + b • z = x := by
  refine ⟨Nat.gcdA a b • x, Nat.gcdB a b • x, ?_⟩
  rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul,
    ← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one, Int.natCast_one, one_smul]

theorem coprime_multiple_subgroups_sup (G : Type*) [AddCommGroup G]
    (a b : ℕ) (hc : a.Coprime b) :
    multipleAddSubgroup G a ⊔ multipleAddSubgroup G b = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, z, rfl⟩ := coprime_multiple_decomposition a b hc x
  exact AddSubgroup.add_mem_sup ⟨y, rfl⟩ ⟨z, rfl⟩

theorem coprime_cyclic_multiple_subgroups (q a b : ℕ) (hc : a.Coprime b) :
    multipleAddSubgroup (ZMod q) a ⊔ multipleAddSubgroup (ZMod q) b = ⊤ :=
  coprime_multiple_subgroups_sup (ZMod q) a b hc

end Hindman168
