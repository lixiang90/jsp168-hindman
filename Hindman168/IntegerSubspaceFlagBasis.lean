import Hindman168.IntegerFlagBasis

namespace Hindman168
open Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (L : Submodule ℤ E) [Module.Finite ℤ L]

theorem integer_subspace_flag_basis_exists (k : ℕ)
    (V : Fin k → Submodule ℝ E) (hV : Antitone V) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℤ L,
      ∀ j, Submodule.span ℤ (b '' {i | (b i : E) ∈ V j}) =
        integerSubspaceIntersection L (V j) := by
  letI : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  letI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  apply split_integer_flag_basis_exists k (fun j => integerSubspaceIntersection L (V j))
  · intro i j hij
    exact Submodule.comap_mono (Submodule.restrictScalars_mono ℤ (hV hij))
  · intro j
    exact integer_subspace_integer_complement_exists L (V j)

end Hindman168
