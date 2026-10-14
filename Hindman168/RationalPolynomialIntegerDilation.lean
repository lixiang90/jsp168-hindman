import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Actual integral values of rational polynomial curves after one positive
integer dilation. The constant coefficient must already be integral; all
other denominators are cleared uniformly over the whole finite family.
The result supplies lattice points, not an additive logarithm lattice. -/

noncomputable section
namespace Hindman168
open Polynomial

 theorem rational_finite_family_integer_multiplier {ι : Type*}
    (s : Finset ι) (q : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i ∈ s, (D : ℚ) * q i ∈ (Int.castRingHom ℚ).range := by
  classical
  let D : ℕ := ∏ i ∈ s, (q i).den
  refine ⟨D, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  intro i hi
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun i => (q i).den) hi
  have hd : ((q i).den : ℚ) * q i = (q i).num := by
    calc ((q i).den : ℚ) * q i = ((q i).den : ℚ) * ((q i).num / (q i).den) :=
           congrArg (((q i).den : ℚ) * ·) (q i).num_div_den.symm
         _ = _ := by field_simp
  refine ⟨(a : ℤ) * (q i).num, ?_⟩
  change (((a : ℤ) * (q i).num : ℤ) : ℚ) = _
  push_cast
  change (a : ℚ) * (q i).num = (D : ℚ) * q i
  dsimp [D]
  rw [ha, Nat.cast_mul]
  calc (a : ℚ) * (q i).num = (a : ℚ) * (((q i).den : ℚ) * q i) := by rw [hd]
       _ = _ := by ring

 theorem rational_polynomial_family_integer_dilation {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℚ)
    (h0 : ∀ i, (p i).coeff 0 ∈ (Int.castRingHom ℚ).range) :
    ∃ D : ℕ, 0 < D ∧ ∀ i (z : ℤ),
      (p i).eval ((D : ℚ) * z) ∈ (Int.castRingHom ℚ).range := by
  classical
  let s : Finset (Σ _ : ι, ℕ) := Finset.univ.sigma (fun i => (p i).support)
  obtain ⟨D, hD, hcoeff⟩ := rational_finite_family_integer_multiplier s
    (fun x => (p x.1).coeff x.2)
  refine ⟨D, hD, ?_⟩
  intro i z
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Subring.sum_mem
  intro k hk
  cases k with
  | zero => simpa using h0 i
  | succ k =>
    have hc : (D : ℚ) * (p i).coeff (k + 1) ∈ (Int.castRingHom ℚ).range := by
      exact hcoeff ⟨i, k + 1⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hk⟩)
    have hd : (D : ℚ) ^ k ∈ (Int.castRingHom ℚ).range :=
      Subring.pow_mem _ (show (D : ℚ) ∈ (Int.castRingHom ℚ).range from ⟨(D : ℤ), by simp⟩) k
    have hz : (z : ℚ) ^ (k + 1) ∈ (Int.castRingHom ℚ).range :=
      Subring.pow_mem _ (show (z : ℚ) ∈ (Int.castRingHom ℚ).range from ⟨z, rfl⟩) (k + 1)
    have heq : (p i).coeff (k + 1) * ((D : ℚ) * z) ^ (k + 1) =
        ((D : ℚ) * (p i).coeff (k + 1)) * ((D : ℚ) ^ k * (z : ℚ) ^ (k + 1)) := by
      simp only [mul_pow, pow_succ]
      ring
    rw [heq]
    exact Subring.mul_mem _ hc (Subring.mul_mem _ hd hz)

 theorem rational_polynomial_integer_dilation (p : Polynomial ℚ)
    (h0 : p.coeff 0 ∈ (Int.castRingHom ℚ).range) :
    ∃ D : ℕ, 0 < D ∧ ∀ z : ℤ,
      p.eval ((D : ℚ) * z) ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨D, hD, hp⟩ := rational_polynomial_family_integer_dilation
    (fun _ : Unit => p) (fun _ => h0)
  exact ⟨D, hD, hp ()⟩

end Hindman168
