import Hindman168.RationalSubspaceScalarExtension

namespace Hindman168
open scoped TensorProduct

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

noncomputable def rationalSubspaceRealBasisOfBasis
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤) (b : Module.Basis ι ℚ W) :
    Module.Basis ι ℝ E :=
  (b.baseChange ℝ).map (rationalSubspaceScalarExtensionEquiv W hdim hspan)

theorem rational_subspace_real_basis_of_basis_apply
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤) (b : Module.Basis ι ℚ W) (i : ι) :
    rationalSubspaceRealBasisOfBasis W hdim hspan b i = (b i : E) := by
  rw [rationalSubspaceRealBasisOfBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, rationalSubspaceScalarExtensionEquiv_tmul, one_smul]

end Hindman168
