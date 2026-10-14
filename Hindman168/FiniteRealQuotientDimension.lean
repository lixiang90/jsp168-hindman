import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Hindman168

theorem finiteRealQuotient_finrank_lt_of_ne_bot {E : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (hV : V ≠ ⊥) :
    Module.finrank ℝ (E ⧸ V) < Module.finrank ℝ E := by
  letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hp := Module.finrank_pos (R := ℝ) (M := V)
  have hr := V.finrank_quotient_add_finrank
  omega

end Hindman168
