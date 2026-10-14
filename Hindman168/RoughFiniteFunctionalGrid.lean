import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Pi
import Mathlib.Tactic

namespace Hindman168
open Module
open scoped Classical
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

noncomputable def roughFiniteFunctionalGrid (b : Basis ι ℝ E) (n : ι → ℕ) (B : ℕ) :
    Finset (E →ₗ[ℝ] ℝ) :=
  (Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).image
    (fun a => b.constr ℝ (fun j => (a j : ℝ)/(n j : ℝ)))

theorem rough_finite_functional_grid_mem (b : Basis ι ℝ E) (n : ι → ℕ)
    (hn : ∀ j, 0 < n j) (B : ℕ) (χ : E →ₗ[ℝ] ℝ)
    (hχ : ∀ j, ∃ m : ℤ, χ ((n j : ℝ) • b j) = (m : ℝ))
    (hbound : ∀ j, |χ ((n j : ℝ) • b j)| ≤ (B : ℝ)) :
    χ ∈ roughFiniteFunctionalGrid b n B := by
  let a : ι → ℤ := fun j => Classical.choose (hχ j)
  have ha : ∀ j, χ ((n j : ℝ) • b j) = (a j : ℝ) :=
    fun j => Classical.choose_spec (hχ j)
  apply Finset.mem_image.mpr
  refine ⟨a, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j
    apply Finset.mem_Icc.mpr
    have hh := hbound j
    rw [ha j, abs_le] at hh
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  · apply b.ext
    intro j
    rw [b.constr_basis]
    have hh := ha j
    rw [map_smul, smul_eq_mul] at hh
    apply (div_eq_iff (by exact_mod_cast Nat.ne_of_gt (hn j))).mpr
    nlinarith

theorem rough_finite_functional_grid_card_le (b : Basis ι ℝ E) (n : ι → ℕ) (B : ℕ) :
    (roughFiniteFunctionalGrid b n B).card ≤
      (Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).card :=
  Finset.card_image_le

end Hindman168
