import Hindman168.RationalSubspaceCoordinates
import Hindman168.RationalCoordinateSpanPreimage

/-! Real spans of actual rational subspaces inside a proved rational
form have exactly their original rational vectors. Compatible original
coordinates and the genuine coordinate-span preimage theorem prove
this; scalar-extension injectivity is no longer an assumed premise. -/

namespace Hindman168
open Set Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

 theorem rationalSubspace_realSpan_map_coordinates
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (U : Submodule ℚ W) :
    (span ℝ (U.map W.subtype : Set E)).map
        (rationalSubspaceRealBasis W hdim hspan).equivFun.toLinearMap =
      realSpanRationalCoordinates
        (U.map (rationalSubspaceBasis W hdim).equivFun.toLinearMap) := by
  let b := rationalSubspaceBasis W hdim
  let c := rationalSubspaceRealBasis W hdim hspan
  have hs : (c.equivFun : E → _) ∘ (W.subtype : W → E) =
      (rationalCoordinateCast (Fin (Module.finrank ℝ E))) ∘ (b.equivFun : W → _) :=
    funext fun w => rationalSubspaceRealBasis_coordinates W hdim hspan w
  rw [Submodule.map_span]
  change span ℝ ((c.equivFun : E → _) '' (U.map W.subtype : Set E)) =
    span ℝ (rationalCoordinateCast (Fin (Module.finrank ℝ E)) ''
      (U.map b.equivFun.toLinearMap : Set (Fin (Module.finrank ℝ E) → ℚ)))
  rw [Submodule.map_coe, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp, hs]
  rfl

 theorem rationalSubspace_mem_realSpan_iff
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (U : Submodule ℚ W) (w : W) :
    (w : E) ∈ span ℝ (U.map W.subtype : Set E) ↔ w ∈ U := by
  constructor
  · intro hw
    have hm : (rationalSubspaceRealBasis W hdim hspan).equivFun (w : E) ∈
        (span ℝ (U.map W.subtype : Set E)).map
          (rationalSubspaceRealBasis W hdim hspan).equivFun.toLinearMap :=
      ⟨(w : E), hw, rfl⟩
    rw [rationalSubspace_realSpan_map_coordinates W hdim hspan,
      rationalSubspaceRealBasis_coordinates W hdim hspan] at hm
    have hq := (rationalCoordinateCast_mem_realSpan_iff _ _).mp hm
    obtain ⟨u, hu, he⟩ := hq
    have huw : u = w := (rationalSubspaceBasis W hdim).equivFun.injective he
    exact huw ▸ hu
  · intro hw
    exact subset_span ⟨w, hw, rfl⟩

 theorem rationalSubspace_realSpan_intersection_eq
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (U : Submodule ℚ W) :
    (span ℝ (U.map W.subtype : Set E)).restrictScalars ℚ ⊓ W = U.map W.subtype := by
  ext v
  constructor
  · intro hv
    let w : W := ⟨v, hv.2⟩
    exact ⟨w, (rationalSubspace_mem_realSpan_iff W hdim hspan U w).mp hv.1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(rationalSubspace_mem_realSpan_iff W hdim hspan U w).mpr hw, w.property⟩

end Hindman168
