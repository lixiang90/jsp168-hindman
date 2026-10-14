import Hindman168.LocalKernelCounts
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic

/-!
# Actual primitive row counts modulo every prime power

A unit coefficient gives a surjective additive linear row by an explicit
one-coordinate preimage. An integer coefficient nonzero modulo a prime
is a unit modulo every power of that prime. Thus the original uniform
prime-power base law has zero-row probability exactly p^(-A), including
the trivial exponent A=0.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def linearRowAddHom {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) : (Fin d → R) →+ R where
  toFun x := ∑ i, c i * x i
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem linearRowAddHom_surjective_of_unit {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) (j : Fin d) (hj : IsUnit (c j)) : Function.Surjective (linearRowAddHom c) := by
  classical
  obtain ⟨u, hu⟩ := hj
  intro y
  let x : Fin d → R := fun i => if i = j then (↑(u⁻¹) : R) * y else 0
  refine ⟨x, ?_⟩
  change (∑ i, c i * x i) = y
  rw [Finset.sum_eq_single j]
  · simp only [x, if_pos rfl]
    rw [← hu, ← mul_assoc]
    simp
  · intro i _ hij
    simp only [x, if_neg hij, mul_zero]
  · intro h
    exact (h (Finset.mem_univ j)).elim

theorem linearRowAddHom_normalized_mass_one {R : Type*} [CommRing R] [Fintype R] {d : ℕ}
    (c : Fin d → R) (j : Fin d) (hj : IsUnit (c j)) :
    normalizedAddKernelMass (linearRowAddHom c) = 1 :=
  normalizedAddKernelMass_surjective _ (linearRowAddHom_surjective_of_unit c j hj)

theorem integer_coefficient_unit_primePower {p : ℕ} (hp : p.Prime) (A : ℕ) (c : ℤ)
    (hc : (c : ZMod p) ≠ 0) : IsUnit (c : ZMod (p ^ A)) := by
  have hnd : ¬ p ∣ c.natAbs := by
    intro h
    exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr (Int.natCast_dvd.mpr h))
  have hNat : p.Coprime c.natAbs := hp.coprime_iff_not_dvd.mpr hnd
  have hInt : IsCoprime (p : ℤ) c := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hNat)
  apply (ZMod.coe_int_isUnit_iff_isCoprime c (p ^ A)).mpr
  simpa only [Nat.cast_pow] using hInt.pow_left (m := A)

theorem primePower_primitive_row_zero_mass {p d A : ℕ} [NeZero p]
    (hp : p.Prime) (c : Fin d → ℤ) (hrow : ∃ j, (c j : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x = 0) = ((p ^ A : ℕ) : ℝ)⁻¹ := by
  obtain ⟨j, hj⟩ := hrow
  let f := linearRowAddHom (fun i => (c i : ZMod (p ^ A)))
  have hf : Function.Surjective f :=
    linearRowAddHom_surjective_of_unit _ j (integer_coefficient_unit_primePower hp A (c j) hj)
  have hpush := uniformFintypeMass_addGroup_push f hf
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod (p ^ A))) f
    (fun y : ZMod (p ^ A) => y = 0)
  rw [hpush, uniformFintypeMass_event_eq, ZMod.card] at hmap
  exact hmap.symm

theorem primePower_primitive_row_normalized_one {p d A : ℕ} [NeZero p]
    (hp : p.Prime) (c : Fin d → ℤ) (hrow : ∃ j, (c j : ZMod p) ≠ 0) :
    (p ^ A : ℕ) * event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x = 0) = 1 := by
  rw [primePower_primitive_row_zero_mass hp c hrow]
  have hn : ((p ^ A : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_ne_zero A hp.ne_zero : (p : ℕ) ^ A ≠ 0)
  exact mul_inv_cancel₀ hn

end Hindman168
