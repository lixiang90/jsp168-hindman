import Hindman168.TorusPolynomialCharacterProjection

namespace Hindman168
open scoped BigOperators Classical

/-- The actual real horizontal character with an integer coordinate vector. -/
noncomputable def torusIntegerCharacter {κ : Type*} [Fintype κ]
    (k : κ → ℤ) : (κ → ℝ) →+ ℝ where
  toFun x := ∑ j, (k j : ℝ)*x j
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem torus_integer_character_continuous {κ : Type*} [Fintype κ] (k : κ → ℤ) :
    Continuous (torusIntegerCharacter k) := by
  change Continuous (fun x : κ → ℝ => ∑ j, (k j : ℝ)*x j)
  fun_prop

theorem torus_integer_character_lattice_value {κ : Type*} [Fintype κ]
    (k z : κ → ℤ) : torusIntegerCharacter k (fun j => (z j : ℝ)) = ((∑ j, k j*z j : ℤ) : ℝ) := by
  dsimp only [torusIntegerCharacter, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  push_cast
  rfl

theorem torus_integer_character_lattice_integral {κ : Type*} [Fintype κ]
    (k z : κ → ℤ) : ∃ a : ℤ, torusIntegerCharacter k (fun j => (z j : ℝ)) = (a : ℝ) :=
  ⟨∑ j, k j*z j, torus_integer_character_lattice_value k z⟩

theorem torus_integer_character_nonzero {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (hk : k ≠ 0) : torusIntegerCharacter k ≠ 0 := by
  intro h
  have hex : ∃ j, k j ≠ 0 := by
    by_contra! hz
    exact hk (funext hz)
  obtain ⟨j, hj⟩ := hex
  have hv := DFunLike.congr_fun h (Pi.single j (1 : ℝ))
  change torusIntegerCharacter k (Pi.single j (1 : ℝ)) = 0 at hv
  have heval : torusIntegerCharacter k (Pi.single j (1 : ℝ)) = (k j : ℝ) := by
    change (∑ i, (k i : ℝ)*(Pi.single j (1 : ℝ) : κ → ℝ) i) = _
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, mul_one]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  rw [heval] at hv
  exact hj (by exact_mod_cast hv)

end Hindman168
