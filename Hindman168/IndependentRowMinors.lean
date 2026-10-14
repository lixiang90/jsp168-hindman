import Hindman168.PrimePowerRowSystems
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# From the paper's row independence to actual local count bounds

Two linearly independent coefficient vectors have a nonzero two-column
minor. Over the prime residue field this integer minor lifts to a unit
at every prime power. Hence the previous exact pair count and full-system
upper bounds apply under the paper's stated independence hypothesis.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem linearIndependent_pair_exists_nonzero_minor {R : Type*} [CommRing R] [Nontrivial R]
    {d : ℕ} (c e : Fin d → R) (h : LinearIndependent R ![c, e]) :
    ∃ j k, c j * e k - c k * e j ≠ 0 := by
  classical
  have hc : c ≠ 0 := by simpa using LinearIndependent.ne_zero (0 : Fin 2) h
  have hex : ∃ j, c j ≠ 0 := by
    by_contra! hz
    exact hc (funext hz)
  obtain ⟨j, hj⟩ := hex
  by_contra! hminor
  have hv : e j • c + (-c j) • e = 0 := by
    funext k
    change e j * c k + (-c j) * e k = 0
    calc
      _ = -(c j * e k - c k * e j) := by ring
      _ = 0 := by rw [hminor j k, neg_zero]
  have hz := (h.eq_zero_of_pair hv).2
  exact hj (neg_eq_zero.mp hz)

theorem primePower_twoRow_mass_of_linearIndependent {p d A B C : ℕ} [NeZero p]
    (hp : p.Prime) (hBA : B ≤ A) (hCA : C ≤ A) (c e : Fin d → ℤ)
    (hrows : LinearIndependent (ZMod p) ![(fun j => (c j : ZMod p)), (fun j => (e j : ZMod p))]) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
          (linearRowAddHom (fun j => (c j : ZMod (p ^ A))) x) = 0 ∧
        ZMod.castHom (pow_dvd_pow p hCA) (ZMod (p ^ C))
          (linearRowAddHom (fun j => (e j : ZMod (p ^ A))) x) = 0) =
      ((p ^ (B + C) : ℕ) : ℝ)⁻¹ := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, k, hminor⟩ := linearIndependent_pair_exists_nonzero_minor _ _ hrows
  apply primePower_twoRow_reduced_divisibility_mass hp hBA hCA c e j k
  simpa only [Int.cast_sub, Int.cast_mul] using hminor

theorem primePowerRowSystem_kernel_le_independent_rows {p q d A : ℕ} [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u v : Fin q)
    (hrows : LinearIndependent (ZMod p)
      ![(fun j => (c u j : ZMod p)), (fun j => (c v j : ZMod p))]) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => primePowerRowSystem p q d A a ha c x = 0) ≤
      ((p ^ (a u + a v) : ℕ) : ℝ)⁻¹ := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, k, hminor⟩ := linearIndependent_pair_exists_nonzero_minor _ _ hrows
  apply primePowerRowSystem_kernel_le_two_rows hp a ha c u v j k
  simpa only [Int.cast_sub, Int.cast_mul] using hminor

theorem primePowerLocalAlpha_le_independent_rows (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u v : Fin q)
    (hrows : LinearIndependent (ZMod p)
      ![(fun j => (c u j : ZMod p)), (fun j => (c v j : ZMod p))]) :
    primePowerLocalAlpha p q d A a ha c ≤
      ((p ^ ((∑ i, a i) - (a u + a v)) : ℕ) : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, k, hminor⟩ := linearIndependent_pair_exists_nonzero_minor _ _ hrows
  apply primePowerLocalAlpha_le_pair p q d A hp a ha c u v j k
  simpa only [Int.cast_sub, Int.cast_mul] using hminor

end Hindman168
