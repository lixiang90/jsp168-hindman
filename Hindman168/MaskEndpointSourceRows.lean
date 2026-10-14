import Hindman168.MaskFiniteElimination
import Hindman168.MaskRawCenteredCorrelation
import Hindman168.MaskRawGeneralCorrelation

/-! Reindex the genuine full mask stage to the original additive source.
The prime law, harmonic base law and normalized integer forms agree.
All bounds remain on the complete original prime support. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass MaskOriginalSampling

noncomputable def maskSourceSupport (m : ℕ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Finset (Fin (m+1)) := ((Fintype.equivFin (LargeColumnSubset m)).symm t).val

theorem maskSourceSupport_card (m : ℕ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    2 ≤ (maskSourceSupport m t).card := ((Fintype.equivFin (LargeColumnSubset m)).symm t).property

noncomputable def maskSourceFullStage (m : ℕ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    TargetedMaskRowStage (maskSourceSupport m t) :=
  fullMaskRowStage (maskSourceSupport m t) (maskSourceSupport_card m t)

abbrev MaskEndpointInput {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) :=
  MaskRowStageInput (maskSourceSupport m t) gap C (maskSourceFullStage m t) w ∅

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def maskEndpointLabel (_w : ℕ) (base : MaskOriginalBaseRow m gap t) : Fin (m+1) :=
  (maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor
    (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target base)

noncomputable def maskEndpointSource {w : ℕ} (D : MaskEndpointInput gap C t w) : MaskCenteredInput gap t :=
  fun x base => D.rows x (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target base)

theorem maskEndpointSource_majorized {w : ℕ} (D : MaskEndpointInput gap C t w) :
    rawMajorizedSourceAdmissible gap C t (maskEndpointLabel gap t) w (maskEndpointSource gap C t D) := by
  intro x hx base y
  exact D.row_bound x hx (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target base) y

theorem maskEndpointSource_originalProduct {w : ℕ} (D : MaskEndpointInput gap C t w)
    (x : Fin (maskSourceFullStage m t).primeArity → ℕ) (z : Fin (m+1) → ℤ) :
    originalProduct gap a C t (fun _ => maskEndpointSource gap C t D) w x z =
      maskRowFunctionProduct (maskSourceFullStage m t).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w) D.rows x z := by
  unfold originalProduct maskRowFunctionProduct
  exact Fintype.prod_equiv (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target)
    _ _ (fun _ => rfl)

theorem maskEndpointSource_correlation {w : ℕ} (D : MaskEndpointInput gap C t w) :
    maskRowStageInputCorrelation (maskSourceSupport m t) gap a C D =
      rawCorrelation gap a C t (fun _ => maskEndpointSource gap C t D) w := by
  unfold maskRowStageInputCorrelation maskRowMaskCorrelation rawCorrelation
  simp only [maskMultiplicativeProduct, Finset.prod_empty, mul_one]
  apply congrArg (expectation (basePrimeMass gap t w))
  funext x
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  exact (maskEndpointSource_originalProduct gap a C t D x z).symm

theorem maskEndpointSource_root {w : ℕ} (D : MaskEndpointInput gap C t w)
    (x : Fin (maskSourceFullStage m t).primeArity → ℕ) :
    maskEndpointSource gap C t D x none = D.rows x (maskSourceFullStage m t).target := rfl

theorem maskEndpointSource_centered_admissible {w : ℕ} (D : MaskEndpointInput gap C t w)
    (hD : maskRowStageInputHasTarget (maskSourceSupport m t) gap C D
      (targetRootCenteredMask gap C t (maskEndpointLabel gap t) w)) :
    rawCenteredSourceAdmissible gap C t (maskEndpointLabel gap t) w (maskEndpointSource gap C t D) := by
  have hb := maskEndpointSource_majorized gap C t D
  refine ⟨?_, hb⟩
  intro x hx
  refine ⟨(maskEndpointSource_root gap C t D x).trans (hD x), ?_⟩
  intro k y
  exact hb x hx.1 (some (additiveRowAssigned _ k)) y

end Hindman168
