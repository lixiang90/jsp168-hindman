import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A constructed continuous linear left inverse to any actual finite
real submodule inclusion. No complement is supplied as a hypothesis. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def finiteRealSubmoduleRetraction (V : Submodule ℝ E) : E →L[ℝ] V :=
  V.subtype.leftInverse.toContinuousLinearMap

theorem finiteRealSubmoduleRetraction_left (V : Submodule ℝ E) (v : V) :
    finiteRealSubmoduleRetraction V v.val = v :=
  LinearMap.leftInverse_apply_of_inj V.ker_subtype v

end Hindman168
