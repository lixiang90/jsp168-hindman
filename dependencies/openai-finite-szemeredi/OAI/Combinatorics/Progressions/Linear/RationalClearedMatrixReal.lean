/- Modified 2026-10-15 for Lean 4.32.2 / mathlib 905b958: compatibility-only lemma renaming. Source: openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. -/
import Mathlib.Data.Real.Basic
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem matrixDenominator_mul_entry_real (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    (matrixDenominator S : ℝ) * (S i j : ℝ) = (clearedMatrix S i j : ℝ) := by
  classical
  have h : (clearedMatrix S i j : ℚ) = (matrixDenominator S : ℚ) * S i j :=
    congrFun (congrFun (clearedMatrix_cast S) i) j
  exact_mod_cast h.symm

theorem matrixDenominator_mul_entry_real_integral (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = (z : ℝ) :=
  ⟨clearedMatrix S i j, matrixDenominator_mul_entry_real S i j⟩

end Erdos3

end

end OAI
