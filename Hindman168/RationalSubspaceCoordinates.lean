import Hindman168.RationalSubspaceScalarExtension
import Hindman168.RationalCoordinateDecomposition

/-! The actual compatible rational/real basis square commutes.
Membership in the ORIGINAL rational subspace is exactly rationality of
the actual real coordinates, with no additional coordinate hypothesis. -/

namespace Hindman168
open Set Submodule Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

 theorem rationalSubspaceRealBasis_coordinates
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (w : W) :
    (rationalSubspaceRealBasis W hdim hspan).equivFun (w : E) =
      rationalCoordinateCast (Fin (Module.finrank ℝ E)) ((rationalSubspaceBasis W hdim).equivFun w) := by
  apply (rationalSubspaceRealBasis W hdim hspan).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Basis.equivFun_symm_apply]
  have he := congrArg (fun z : W => (z : E))
    ((rationalSubspaceBasis W hdim).sum_equivFun w)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  symm
  calc
    _ = ∑ i, ((rationalSubspaceBasis W hdim).equivFun w i) •
        (rationalSubspaceBasis W hdim i : E) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rationalSubspaceRealBasis_apply]
      exact Rat.cast_smul_eq_qsmul ℝ _ _
    _ = (w : E) := he

 theorem rationalSubspace_mem_iff_coordinates
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (v : E) :
    v ∈ W ↔ (rationalSubspaceRealBasis W hdim hspan).equivFun v ∈
      range (rationalCoordinateCast (Fin (Module.finrank ℝ E))) := by
  constructor
  · intro hv
    exact ⟨(rationalSubspaceBasis W hdim).equivFun ⟨v, hv⟩,
      (rationalSubspaceRealBasis_coordinates W hdim hspan ⟨v, hv⟩).symm⟩
  · rintro ⟨q, hq⟩
    let w := (rationalSubspaceBasis W hdim).equivFun.symm q
    have he := rationalSubspaceRealBasis_coordinates W hdim hspan w
    rw [LinearEquiv.apply_symm_apply] at he
    have hwv : (w : E) = v :=
      (rationalSubspaceRealBasis W hdim hspan).equivFun.injective (he.trans hq)
    exact hwv ▸ w.property

 theorem rationalSubspace_mem_iff_each_coordinate
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (v : E) :
    v ∈ W ↔ ∀ i, ∃ q : ℚ, (rationalSubspaceRealBasis W hdim hspan).repr v i = (q : ℝ) := by
  rw [rationalSubspace_mem_iff_coordinates W hdim hspan v]
  constructor
  · rintro ⟨q, hq⟩ i
    exact ⟨q i, (congrFun hq i).symm⟩
  · intro h
    classical
    choose q hq using h
    exact ⟨q, funext fun i => (hq i).symm⟩

end Hindman168
