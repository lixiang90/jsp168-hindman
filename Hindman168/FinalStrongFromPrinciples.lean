import Hindman168.FinalNativeInverseStep
import Hindman168.FinalUniformAlignmentInput
import Hindman168.FiniteScaleNativeUnitModels
import Hindman168.FiniteToStrong

/-! Final Section 2.5 assembly from the two precise remaining paper inputs.
Ramsey selection, generated master parameters, tolerance choices, prediction
limits, actual positive counts, finite extraction and strong separation are
all discharged by proved theorems. No form of the conclusion is an input. -/
namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

theorem finiteConjecture_of_native_inverse_and_alignment
    (hinverse : ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t-1) t)
    (halignment : HasUniformSelectedPrincipalAlignment.{u}) : FiniteConjecture := by
  intro r χ m
  obtain ⟨s,hs⟩ := native_inverse_mask_family_of_degree_minus_one hinverse m
  obtain ⟨n,hn⟩ := principal_product_chain_selection (m+1) r
  obtain ⟨B,A,hclosed,_hBne,_hBpos,hA,δ,hδ,halign⟩ := halignment n r s
  obtain ⟨θ,η,hθ,_hθsmall,hη,hfinal⟩ := principal_final_deduction_tolerances
    n m r B A hclosed δ hδ
  obtain ⟨J,hJ,κ,τ,hκ,hτ,hτcap,hτκ,N,hN⟩ :=
    finite_scale_prediction_models_unit_observables.{u} A hA r n m s hs η hη η hη
  let M := N+1
  have hM : 0 < M := Nat.succ_pos N
  let gap₀ : ℕ → Fin M := fun _ => ⟨0,hM⟩
  let F := maskGeneratedMaster m gap₀
  have hF := maskGeneratedMaster_conditions m gap₀ A hA
  obtain ⟨f,hf,hd,hselected⟩ := hN M hM (by dsimp [M]; omega) χ
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨e,heM,_hadmissible,model,hlimits,hmodel,_rest⟩ := hselected U hU
  let S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ :=
    fun T i γ w y => (model T i γ).val w y
  have hS : ∀ T i γ w y, S T i γ w y ∈ Set.Icc (0 : ℝ) 1 :=
    fun T i γ w y => (hmodel T i γ).2.1 w y
  have hlim := halign (maskMasterArity m) M hM
    (originalRowMasterCatalog (maskGeneratedRowDataFamily m gap₀)) F hF e heM S
    (fun T i γ => (hmodel T i γ).1) hS θ hθ
  obtain ⟨W,hW,_hpositive,hmono⟩ := hfinal (maskMasterArity m) M
    (originalRowMasterCatalog (maskGeneratedRowDataFamily m gap₀)) F hF hn e heM U hU χ S
    hlimits hS hlim
  exact ⟨W,by omega,hmono⟩

/-- The original StrongConjecture, including all separation parameters,
now needs only the original inverse family and uniform selected alignment.
The zero-color case is vacuous; target size zero is covered without any
positive-size assumption. First-order inverse is proved, not assumed. -/
theorem strongConjecture_of_native_inverse_and_alignment
    (hinverse : ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t-1) t)
    (halignment : HasUniformSelectedPrincipalAlignment.{u}) : StrongConjecture :=
  finite_implies_strong (finiteConjecture_of_native_inverse_and_alignment hinverse halignment)
end Hindman168
