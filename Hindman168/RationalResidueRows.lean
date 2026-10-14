import Hindman168.RationalDivisorMasks
import Hindman168.PrimitiveLinearRows
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Unit-denominator residue rows

The residue of a cleared rational coefficient b/a is defined using the
inverse of a in ZMod k. No ring homomorphism from all of Q to ZMod k
is assumed. Unit scaling preserves zero fibers, primitive rows and
linear independence, even at composite moduli and modulus one.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def unitDenominatorRow {d : ℕ} (k a : ℕ) (b : Fin d → ℤ) : Fin d → ZMod k :=
  fun j => (a : ZMod k)⁻¹ * (b j : ZMod k)

theorem unitDenominatorRow_scale {d : ℕ} {k a : ℕ} (h : a.Coprime k)
    (b : Fin d → ℤ) (j : Fin d) :
    (a : ZMod k) * unitDenominatorRow k a b j = (b j : ZMod k) := by
  rw [unitDenominatorRow, ← mul_assoc, ZMod.coe_mul_inv_eq_one a h, one_mul]

theorem unitDenominatorRow_zero_iff {d : ℕ} {k a : ℕ} (h : a.Coprime k)
    (b : Fin d → ℤ) (j : Fin d) :
    unitDenominatorRow k a b j = 0 ↔ (b j : ZMod k) = 0 := by
  constructor
  · intro hz
    rw [← unitDenominatorRow_scale h b j, hz, mul_zero]
  · intro hz
    simp only [unitDenominatorRow, hz, mul_zero]

theorem unitDenominatorRow_primitive_iff {d : ℕ} {k a : ℕ} (h : a.Coprime k)
    (b : Fin d → ℤ) :
    (∃ j, unitDenominatorRow k a b j ≠ 0) ↔ ∃ j, (b j : ZMod k) ≠ 0 := by
  exact exists_congr (fun j => not_congr (unitDenominatorRow_zero_iff h b j))

theorem unitDenominatorRow_linear_zero_iff {d : ℕ} {k a : ℕ} (h : a.Coprime k)
    (b : Fin d → ℤ) (x : Fin d → ZMod k) :
    linearRowAddHom (unitDenominatorRow k a b) x = 0 ↔
      linearRowAddHom (fun j => (b j : ZMod k)) x = 0 := by
  have he : linearRowAddHom (unitDenominatorRow k a b) x =
      (a : ZMod k)⁻¹ * linearRowAddHom (fun j => (b j : ZMod k)) x := by
    change (∑ j, ((a : ZMod k)⁻¹ * (b j : ZMod k)) * x j) = _
    change (∑ j, ((a : ZMod k)⁻¹ * (b j : ZMod k)) * x j) =
      (a : ZMod k)⁻¹ * (∑ j, (b j : ZMod k) * x j)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _)
  rw [he]
  change ((↑((ZMod.unitOfCoprime a h)⁻¹) : ZMod k) *
    linearRowAddHom (fun j => (b j : ZMod k)) x = 0) ↔ _
  exact Units.mul_right_eq_zero _

theorem unitDenominatorRows_linearIndependent_iff {q d : ℕ} (k : ℕ)
    (a : Fin q → ℕ) (b : Fin q → Fin d → ℤ) (h : ∀ u, (a u).Coprime k) :
    LinearIndependent (ZMod k) (fun u => unitDenominatorRow k (a u) (b u)) ↔
      LinearIndependent (ZMod k) (fun u j => (b u j : ZMod k)) := by
  let v := fun u j => (b u j : ZMod k)
  let w := fun u => (ZMod.unitOfCoprime (a u) (h u))⁻¹
  have he : (fun u => unitDenominatorRow k (a u) (b u)) = w • v := by
    funext u j
    rfl
  rw [he]
  exact LinearIndependent.units_smul_iff v w

theorem unitDenominatorRow_pairIndependent_iff {d : ℕ} {k a e : ℕ}
    (ha : a.Coprime k) (he : e.Coprime k) (b c : Fin d → ℤ) :
    LinearIndependent (ZMod k) ![unitDenominatorRow k a b, unitDenominatorRow k e c] ↔
      LinearIndependent (ZMod k) ![(fun j => (b j : ZMod k)), (fun j => (c j : ZMod k))] := by
  let v : Fin 2 → Fin d → ZMod k := ![(fun j => (b j : ZMod k)), (fun j => (c j : ZMod k))]
  let w : Fin 2 → (ZMod k)ˣ := ![(ZMod.unitOfCoprime a ha)⁻¹, (ZMod.unitOfCoprime e he)⁻¹]
  have hv : ![unitDenominatorRow k a b, unitDenominatorRow k e c] = w • v := by
    funext u j
    fin_cases u <;> rfl
  rw [hv]
  exact LinearIndependent.units_smul_iff v w

end Hindman168
