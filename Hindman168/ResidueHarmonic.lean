import Hindman168.HarmonicProgression
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Harmonic mass in one residue class on an arbitrary real interval

The natural-number interval `Ico (ceil A) (ceil B)` is exactly the integer
points of the real half-open interval `[A,B)`. Enumeration starts with the
unique representative in the first complete `q`-term interval. This handles
nonintegral endpoints and empty residue classes without a rounding loss.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def residueWindow (A B : ℝ) (q a : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => n % q = a)

noncomputable def residueHarmonic (A B : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ residueWindow A B q a, (n : ℝ)⁻¹

theorem residue_enumeration {A B : ℝ} {q a s : ℕ} (hq : 0 < q)
    (hs : s ∈ Finset.Ico ⌈A⌉₊ (⌈A⌉₊ + q)) (hsmod : s % q = a) :
    residueHarmonic A B q a =
      progressionHarmonic s q ⌈(B - (s : ℝ)) / q⌉₊ := by
  classical
  let n : ℕ := ⌈(B - (s : ℝ)) / q⌉₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' := Finset.mem_Ico.mp hs
  have hwin : residueWindow A B q a =
      (Finset.range n).image (fun j => s + q * j) := by
    ext m
    simp only [residueWindow, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hmlo, hmhi⟩, hmod⟩
      have hsm : s ≤ m := by
        by_contra h
        have hmrange : m ∈ Finset.Ico ⌈A⌉₊ (⌈A⌉₊ + q) :=
          Finset.mem_Ico.mpr ⟨hmlo, by omega⟩
        have he := Nat.mod_injOn_Ico ⌈A⌉₊ q hs hmrange (hsmod.trans hmod.symm)
        omega
      have hdvd : q ∣ m - s := (Nat.modEq_iff_dvd' hsm).mp (hsmod.trans hmod.symm)
      let j : ℕ := (m - s) / q
      have hjm : s + q * j = m := by
        dsimp [j]
        rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
        omega
      have hjmR : (s : ℝ) + (q : ℝ) * j = m := by exact_mod_cast hjm
      have hmB : (m : ℝ) < B := Nat.lt_ceil.mp hmhi
      have hjn : j < n := by
        apply Nat.lt_ceil.mpr
        apply (lt_div_iff₀ hqR).mpr
        nlinarith
      exact ⟨j, hjn, hjm⟩
    · rintro ⟨j, hjn, rfl⟩
      have hjB : (j : ℝ) < (B - (s : ℝ)) / q := Nat.lt_ceil.mp hjn
      have hmB : (s + q * j : ℕ) < ⌈B⌉₊ := by
        apply Nat.lt_ceil.mpr
        have hjmul := (lt_div_iff₀ hqR).mp hjB
        simp only [Nat.cast_add, Nat.cast_mul]
        nlinarith
      refine ⟨⟨by omega, hmB⟩, ?_⟩
      rw [Nat.add_mul_mod_self_left, hsmod]
  have hinj : Function.Injective (fun j : ℕ => s + q * j) := by
    intro i j hij
    exact mul_left_cancel₀ hq.ne' (Nat.add_left_cancel hij)
  rw [residueHarmonic, hwin, Finset.sum_image hinj.injOn]
  simp only [Nat.cast_add, Nat.cast_mul]
  rfl

/-- The paper's exact `1/A` discrepancy for one occupied residue class. -/
theorem residue_harmonic_error {A B : ℝ} {q a : ℕ}
    (hA : 0 < A) (hAB : A < B) (hq : 0 < q) (ha : a < q) :
    |residueHarmonic A B q a - Real.log (B / A) / q| ≤ A⁻¹ := by
  classical
  have ha' : a ∈ (Finset.Ico ⌈A⌉₊ (⌈A⌉₊ + q)).image (fun n => n % q) := by
    rw [Nat.image_Ico_mod]
    exact Finset.mem_range.mpr ha
  obtain ⟨s, hs, hsmod⟩ := Finset.mem_image.mp ha'
  let n : ℕ := ⌈(B - (s : ℝ)) / q⌉₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' := Finset.mem_Ico.mp hs
  have hAs : A ≤ (s : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hs'.1)
  have hsAq : (s : ℝ) ≤ A + q := by
    have hsle : s + 1 ≤ ⌈A⌉₊ + q := by omega
    have hsleR : (s : ℝ) + 1 ≤ (⌈A⌉₊ : ℝ) + q := by exact_mod_cast hsle
    have hc := Nat.ceil_lt_add_one hA.le
    linarith
  have hcover : B ≤ (s : ℝ) + q * n := by
    have hc := (div_le_iff₀ hqR).mp (Nat.le_ceil ((B - (s : ℝ)) / q))
    dsimp [n]
    nlinarith
  have hpoints : ∀ j < n, (s : ℝ) + q * j < B := by
    intro j hj
    have hc := (lt_div_iff₀ hqR).mp (Nat.lt_ceil.mp hj)
    nlinarith
  rw [residue_enumeration hq hs hsmod]
  exact progression_harmonic_error n hA hAB hqR hAs hsAq hcover hpoints

end Hindman168
