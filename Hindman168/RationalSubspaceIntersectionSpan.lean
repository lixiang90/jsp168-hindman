import Hindman168.RationalSubspaceSpanIntersection
import Hindman168.RationalCoordinateIntersection

namespace Hindman168
open Set Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

theorem rationalSubspace_realSpan_inf
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (U T : Submodule ℚ W) :
    span ℝ ((U ⊓ T).map W.subtype : Set E) =
      span ℝ (U.map W.subtype : Set E) ⊓ span ℝ (T.map W.subtype : Set E) := by
  let c := (rationalSubspaceRealBasis W hdim hspan).equivFun
  let a := (rationalSubspaceBasis W hdim).equivFun
  apply Submodule.map_injective_of_injective c.injective
  rw [Submodule.map_inf _ c.injective]
  rw [rationalSubspace_realSpan_map_coordinates W hdim hspan,
    rationalSubspace_realSpan_map_coordinates W hdim hspan,
    rationalSubspace_realSpan_map_coordinates W hdim hspan]
  rw [Submodule.map_inf _ a.injective, realSpanRationalCoordinates_inf]

theorem rationalSubspace_rational_intersection
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (V T : Submodule ℝ E)
    (hV : span ℝ ((V.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = V)
    (hT : span ℝ ((T.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = T) :
    span ℝ (((V ⊓ T).restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = V ⊓ T := by
  let U := (V.restrictScalars ℚ).comap W.subtype
  let N := (T.restrictScalars ℚ).comap W.subtype
  have hu : U.map W.subtype = V.restrictScalars ℚ ⊓ W := by
    rw [Submodule.map_comap_subtype, inf_comm]
  have hn : N.map W.subtype = T.restrictScalars ℚ ⊓ W := by
    rw [Submodule.map_comap_subtype, inf_comm]
  have hi : (U ⊓ N).map W.subtype = (V ⊓ T).restrictScalars ℚ ⊓ W := by
    rw [Submodule.map_inf _ W.subtype_injective, hu, hn]
    ext x
    change ((x ∈ V ∧ x ∈ W) ∧ x ∈ T ∧ x ∈ W) ↔ (x ∈ V ∧ x ∈ T) ∧ x ∈ W
    tauto
  rw [← hi, rationalSubspace_realSpan_inf W hdim hspan U N, hu, hn, hV, hT]

end Hindman168
