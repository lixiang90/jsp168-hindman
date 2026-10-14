import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A concrete full integer lattice and rational real line do not have
unconditional relative layer lifts through an arbitrary real quotient.
This identifies a missing hypothesis in a proposed construction, not an
obstruction to the original nilpotent-group theorem. -/

namespace Hindman168

def liftReviewIntegerPlane : Submodule ℤ (ℝ × ℝ) where
  carrier := {x | ∃ a b : ℤ, x = ((a : ℝ), (b : ℝ))}
  zero_mem' := ⟨0, 0, by ext <;> norm_num⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a+c, b+d, by simp⟩
  smul_mem' := by
    rintro n x ⟨a, b, rfl⟩
    refine ⟨n*a, n*b, ?_⟩
    ext <;> simp [zsmul_eq_mul]

def liftReviewRationalLine : Submodule ℝ (ℝ × ℝ) :=
  LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - (2 : ℝ) • LinearMap.snd ℝ ℝ ℝ)

theorem integer_layer_relative_lift_not_unconditional :
    (1 : ℝ) ∈ liftReviewIntegerPlane.map ((LinearMap.fst ℝ ℝ ℝ).restrictScalars ℤ) ∧
    (1 : ℝ) ∈ liftReviewRationalLine.map (LinearMap.fst ℝ ℝ ℝ) ∧
    (1 : ℝ) ∉ (liftReviewIntegerPlane ⊓ liftReviewRationalLine.restrictScalars ℤ).map
      ((LinearMap.fst ℝ ℝ ℝ).restrictScalars ℤ) := by
  refine ⟨⟨(1, 0), ⟨1, 0, by simp⟩, rfl⟩, ?_, ?_⟩
  · refine ⟨(1, 1/2), ?_, rfl⟩
    change (1 : ℝ)-2*(1/2) = 0
    norm_num
  · rintro ⟨x, ⟨⟨a, b, rfl⟩, hV⟩, hq⟩
    change (a : ℝ)-2*(b : ℝ) = 0 at hV
    change (a : ℝ) = 1 at hq
    have ha : a = 1 := by exact_mod_cast hq
    have he : a-2*b = 0 := by exact_mod_cast hV
    omega

end Hindman168
