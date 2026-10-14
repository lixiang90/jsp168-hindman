import Hindman168.RationalSubspaceRealBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! The NATURAL scalar-extension map r tensor w -> r*w in the original
real space is a genuine real linear equivalence for a full rational
subspace of the proved correct dimension. Equality on an actual tensor
basis identifies the constructed inverse with this natural map. -/

namespace Hindman168
open Set Submodule Module
open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

noncomputable def rationalSubspaceScalarExtensionMap (W : Submodule ℚ E) :
    (ℝ ⊗[ℚ] W) →ₗ[ℝ] E :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ (W →ₗ[ℚ] E) W.subtype)

 theorem rationalSubspaceScalarExtensionMap_tmul (W : Submodule ℚ E) (r : ℝ) (w : W) :
    rationalSubspaceScalarExtensionMap W (r ⊗ₜ[ℚ] w) = r • (w : E) := rfl

variable (W : Submodule ℚ E) [FiniteDimensional ℚ W]

noncomputable def rationalSubspaceScalarExtensionEquiv
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) : (ℝ ⊗[ℚ] W) ≃ₗ[ℝ] E :=
  (rationalSubspaceBasis W hdim).baseChange ℝ |>.equiv
    (rationalSubspaceRealBasis W hdim hspan) (Equiv.refl _)

 theorem rationalSubspaceScalarExtensionEquiv_toLinearMap
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) :
    (rationalSubspaceScalarExtensionEquiv W hdim hspan).toLinearMap =
      rationalSubspaceScalarExtensionMap W := by
  apply ((rationalSubspaceBasis W hdim).baseChange ℝ).ext
  intro i
  change (rationalSubspaceScalarExtensionEquiv W hdim hspan)
      (((rationalSubspaceBasis W hdim).baseChange ℝ) i) = _
  rw [rationalSubspaceScalarExtensionEquiv, Basis.equiv_apply,
    rationalSubspaceRealBasis_apply, Basis.baseChange_apply,
    rationalSubspaceScalarExtensionMap_tmul, one_smul]
  rfl

 theorem rationalSubspaceScalarExtensionMap_bijective
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) :
    Function.Bijective (rationalSubspaceScalarExtensionMap W) := by
  rw [← rationalSubspaceScalarExtensionEquiv_toLinearMap W hdim hspan]
  exact (rationalSubspaceScalarExtensionEquiv W hdim hspan).bijective

 theorem rationalSubspaceScalarExtensionEquiv_tmul
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (r : ℝ) (w : W) :
    rationalSubspaceScalarExtensionEquiv W hdim hspan (r ⊗ₜ[ℚ] w) = r • (w : E) :=
  (congrArg (fun f : (ℝ ⊗[ℚ] W) →ₗ[ℝ] E => f (r ⊗ₜ[ℚ] w))
    (rationalSubspaceScalarExtensionEquiv_toLinearMap W hdim hspan)).trans
      (rationalSubspaceScalarExtensionMap_tmul W r w)

end Hindman168
