import Hindman168.RationalSubspaceScalarExtension
import Mathlib.RingTheory.Flat.Basic

/-! Real linear independence and exact dimensions for EVERY actual
Q subspace of a proved full rational form. Flat base change preserves
Q independence in the tensor product; the proved injective NATURAL
map to the original E transports it to real independence in E. -/

namespace Hindman168
open Set Submodule Module
open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

 theorem rationalSubspace_linearIndependent_real
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤)
    {ι : Type*} (v : ι → E) (hQ : LinearIndependent ℚ v)
    (hv : ∀ i, v i ∈ W) : LinearIndependent ℝ v := by
  let w : ι → W := fun i => ⟨v i, hv i⟩
  have hw : LinearIndependent ℚ w := LinearIndependent.of_comp W.subtype hQ
  have ht : LinearIndependent ℝ (fun i => (1 : ℝ) ⊗ₜ[ℚ] w i) :=
    Module.Flat.linearIndependent_one_tmul hw
  have he := ht.map' (rationalSubspaceScalarExtensionMap W)
    (LinearMap.ker_eq_bot.mpr
      (rationalSubspaceScalarExtensionMap_bijective W hdim hspan).injective)
  change LinearIndependent ℝ (fun i => rationalSubspaceScalarExtensionMap W ((1 : ℝ) ⊗ₜ[ℚ] w i)) at he
  simpa only [rationalSubspaceScalarExtensionMap_tmul, one_smul] using he

 theorem rationalSubspace_subspace_realSpan_finrank
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (U : Submodule ℚ E) (hU : U ≤ W) :
    Module.finrank ℝ (span ℝ (U : Set E)) = Module.finrank ℚ U := by
  letI := Submodule.finiteDimensional_of_le hU
  let b := Module.finBasis ℚ U
  have hQ : LinearIndependent ℚ (fun i => (b i : E)) :=
    b.linearIndependent.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hR : LinearIndependent ℝ (fun i => (b i : E)) :=
    rationalSubspace_linearIndependent_real W hdim hspan _ hQ (fun i => hU (b i).property)
  have hq : span ℚ (range (fun i => (b i : E))) = U := by
    have he : U.subtype '' range b = range (fun i => (b i : E)) :=
      (Set.range_comp _ _).symm
    rw [← he, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hr : span ℝ (range (fun i => (b i : E))) = span ℝ (U : Set E) := by
    rw [← span_span_of_tower (R := ℚ) (S := ℝ), hq]
  rw [← hr, finrank_span_eq_card hR]
  exact Fintype.card_fin _

end Hindman168
