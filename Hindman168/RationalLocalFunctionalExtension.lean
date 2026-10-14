import Hindman168.RationalSubspaceFunctional
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Rationality on a rational SUBSPACE suffices to choose an ambient real
extension rational on the entire specified rational form. Its values on the
original subspace are unchanged. This removes a global-extension assumption
from actual level-character applications. -/
namespace Hindman168
open Set Submodule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

theorem rational_local_map_lift (U : Submodule ℚ E)
    (ell : E →ₗ[ℝ] ℝ)
    (hRat : ∀ v ∈ U, ∃ q : ℚ, ell v = (q : ℝ)) :
    ∃ f : U →ₗ[ℚ] ℚ, ∀ v : U, (f v : ℝ) = ell v := by
  classical
  let value (v : U) : ℚ := Classical.choose (hRat v v.property)
  have hvalue (v : U) : (value v : ℝ) = ell v :=
    (Classical.choose_spec (hRat v v.property)).symm
  let fU : U →ₗ[ℚ] ℚ := {
    toFun := value
    map_add' := by
      intro a b
      apply Rat.cast_injective (α := ℝ)
      calc
        (value (a+b) : ℝ) = ell (a+b : U) := hvalue _
        _ = ell a + ell b := ell.map_add _ _
        _ = (value a + value b : ℚ) := by rw [Rat.cast_add, hvalue, hvalue]
    map_smul' := by
      intro r v
      change value (r • v) = r * value v
      apply Rat.cast_injective (α := ℝ)
      calc
        (value (r • v) : ℝ) = ell (r • v : U) := hvalue _
        _ = (r : ℝ) * ell v := by
          change ell (r • (v : E)) = (r : ℝ) * ell v
          rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, smul_eq_mul]
        _ = (r * value v : ℚ) := by rw [Rat.cast_mul, hvalue] }
  exact ⟨fU,hvalue⟩

theorem rational_local_functional_extension
    (W : Submodule ℚ E) [FiniteDimensional ℚ W]
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤)
    (S : Submodule ℝ E)
    (hS : span ℝ ((S.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = S)
    (ell : E →ₗ[ℝ] ℝ)
    (hRat : ∀ v ∈ S, v ∈ W → ∃ q : ℚ, ell v = (q : ℝ)) :
    ∃ phi : E →ₗ[ℝ] ℝ, (∀ v ∈ S, phi v = ell v) ∧
      ∀ v ∈ W, ∃ q : ℚ, phi v = (q : ℝ) := by
  let U : Submodule ℚ E := S.restrictScalars ℚ ⊓ W
  obtain ⟨fU,hvalue⟩ := rational_local_map_lift U ell (fun v hv => hRat v hv.1 hv.2)
  obtain ⟨fE, hfE⟩ := fU.exists_extend
  let fW : W →ₗ[ℚ] ℚ := fE.comp W.subtype
  let phi : E →ₗ[ℝ] ℝ := rationalSubspaceFunctional W hdim hspan fW
  have hPhi (w : W) : phi (w : E) = (fW w : ℝ) :=
    rationalSubspaceFunctional_apply (E := E) W hdim hspan fW w
  have hAgree : span ℝ (U : Set E) ≤ LinearMap.eqLocus phi ell := by
    apply span_le.mpr
    intro v hv
    change phi v = ell v
    calc
      phi v = (fW ⟨v,hv.2⟩ : ℝ) := hPhi ⟨v,hv.2⟩
      _ = (fE v : ℝ) := rfl
      _ = (fU ⟨v,hv⟩ : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) (LinearMap.congr_fun hfE ⟨v,hv⟩)
      _ = ell v := hvalue _
  rw [hS] at hAgree
  refine ⟨phi, fun v hv => hAgree hv, ?_⟩
  intro v hv
  exact ⟨fW ⟨v,hv⟩, hPhi ⟨v,hv⟩⟩

end Hindman168
