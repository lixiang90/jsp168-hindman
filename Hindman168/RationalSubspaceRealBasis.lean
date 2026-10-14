import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A genuine full rational subspace of the correct rational dimension
has a rational basis whose SAME columns form a real basis. No
real independence or scalar-extension injectivity is supplied. -/

namespace Hindman168
open Set Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

noncomputable def rationalSubspaceBasis (hdim : Module.finrank ℚ W = Module.finrank ℝ E) :
    Basis (Fin (Module.finrank ℝ E)) ℚ W :=
  Module.finBasisOfFinrankEq ℚ W hdim

 theorem rationalSubspaceBasis_rational_span
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E) :
    span ℚ (range (fun i => (rationalSubspaceBasis W hdim i : E))) = W := by
  have he : W.subtype '' range (rationalSubspaceBasis W hdim) =
      range (fun i => (rationalSubspaceBasis W hdim i : E)) := (Set.range_comp _ _).symm
  rw [← he, ← Submodule.map_span, (rationalSubspaceBasis W hdim).span_eq,
    Submodule.map_top, Submodule.range_subtype]

 theorem rationalSubspaceBasis_real_span
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) :
    span ℝ (range (fun i => (rationalSubspaceBasis W hdim i : E))) = ⊤ := by
  rw [← span_span_of_tower (R := ℚ) (S := ℝ),
    rationalSubspaceBasis_rational_span W hdim]
  exact hspan

 theorem rationalSubspaceBasis_real_linearIndependent
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) :
    LinearIndependent ℝ (fun i => (rationalSubspaceBasis W hdim i : E)) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (rationalSubspaceBasis_real_span W hdim hspan).ge (Fintype.card_fin _)

noncomputable def rationalSubspaceRealBasis
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) : Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Basis.mk (rationalSubspaceBasis_real_linearIndependent W hdim hspan)
    (rationalSubspaceBasis_real_span W hdim hspan).ge

 theorem rationalSubspaceRealBasis_apply
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (i : Fin (Module.finrank ℝ E)) :
    rationalSubspaceRealBasis W hdim hspan i = (rationalSubspaceBasis W hdim i : E) :=
  congrFun (Basis.coe_mk _ _) i

end Hindman168
