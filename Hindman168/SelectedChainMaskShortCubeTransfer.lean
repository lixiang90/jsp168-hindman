import Hindman168.MaskMasterGapIndependence
import Hindman168.MaskRenamedShortCubeLaw
import Hindman168.SelectedChainIndices
import Hindman168.MasterGapIndex

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical

/-- Apply original master short-cube bounds to every target on one
selected chain. All function inputs are the same integer functions. -/
theorem selected_chain_mask_correlation_of_shortCube {ι : Type*} {n m M : ℕ}
    (hM : 0 < M) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : Chain (m+1)) (hC : ∀ i, C.block i ⊆ energyPrincipalSet e)
    (p : Fin (m+1) → Fin n) (hp : ∀ i, energyPrincipal e (p i) = C.pivot i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (J : ℕ) (hJ : 0 < J)
    (F : MasterParameterFamily)
    (hmaster : F = maskGeneratedMaster m (fun _ : ℕ => (⟨0, hM⟩ : Fin M)))
    (f : Finset ℕ → ℕ → ι → ℕ → ℤ → ℝ)
    (model : Finset (Fin n) → Fin n → ι → ℕ → ℤ → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hshort : ∀ i γ (q : Fin (maskRowCountBound m + 1))
      (pol : MvPolynomial (Fin (maskMasterArity m)) ℤ),
      pol ∈ originalRowMasterCatalog (maskGeneratedRowDataFamily m
        (fun _ : ℕ => (⟨0, hM⟩ : Fin M))) →
      ∀ P : Finset (MvPolynomial (Fin (maskMasterArity m)) ℤ),
        (∀ v ∈ P, v ≠ 0) → pol ∈ P → ∀ᶠ w in (U : Filter ℕ),
          expectation (conditionMass (dyadicPoolTupleMass
            (fun _ : Fin (maskMasterArity m) => F.pool w (energyPadding e (p 0))))
            (primeSampleGood P)) (fun x =>
            |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
              (F.gap w (energyPadding e (p 0))) (F.cutoff w (energyPrincipal e (p i)))
              q.val J pol (fun y => f (C.tail i) (energyPrincipal e (p i)) γ w y -
                model (principalTailPositions e (C.tail i)) (p i) γ w y) x|) <
            maskUniformDetectionTolerance m ε / 2) :
    let gap := masterGapIndex M hM (energyPadding e (p 0))
    ∀ (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
      (z : Fin (Fintype.card (LargeColumnSubset m))) (γ : ι)
      (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
      (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
      (_hH : ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w))
      (_htarget : ∀ᶠ w in (U : Filter ℕ),
        H w (maskSourceNonemptySupport m z) = fun y =>
          f (C.tail (targetRootAnchor gap z)) (C.pivot (targetRootAnchor gap z)) γ w y -
            model (principalTailPositions e (C.tail (targetRootAnchor gap z)))
              (p (targetRootAnchor gap z)) γ w y),
      ∀ᶠ w in (U : Filter ℕ),
        |maskOriginalSubsetCorrelation gap a (fun _ => C) w (H w) (b w)| ≤ ε := by
  intro gap a ha z γ H b hH htarget
  let gap₀ : ℕ → Fin M := fun _ => ⟨0, hM⟩
  let l := energyPadding e (p 0)
  have hl : l < M := heM _
  have hgapval (w : ℕ) : (gap w).val = l := masterGapIndex_val M hM l w hl
  have hm : maskGeneratedMaster m gap = F :=
    (maskGeneratedMaster_gap_independent m gap gap₀).trans hmaster.symm
  have hCrange : ∀ i, C.block i ⊆ Finset.range M := by
    intro i y hy
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC i hy)
    exact Finset.mem_range.mpr (heM _)
  have hpad := selected_chain_common_padding e C hC p hp
  have hg : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ C.pivot col := by
    apply Eventually.of_forall
    intro w col
    rw [hgapval]
    exact (hpad.2.2 col).1.trans (hpad.2.2 col).2.le
  have ht : ∀ᶠ w in atTop, ∀ col, C.tail col ⊆ Finset.range (gap w).val := by
    apply Eventually.of_forall
    intro w col y hy
    rw [hgapval]
    exact Finset.mem_range.mpr (hpad.2.1 col y hy)
  let pol := MvPolynomial.rename (maskGeneratedRowDataFamily m gap z).slot
    (targetPredictionPolynomial gap z)
  let P := ((maskGeneratedRowDataFamily m gap z).rows.catalog
    (maskGeneratedRowDataFamily m gap z).target).image
      (MvPolynomial.rename (maskGeneratedRowDataFamily m gap z).slot)
  have hden : targetPredictionPolynomial gap z ∈
      (maskGeneratedRowDataFamily m gap z).rows.catalog (maskGeneratedRowDataFamily m gap z).target :=
    (maskGeneratedRowDataFamily m gap z).rows.denominator_mem_catalog _
  have hpol : pol ∈ originalRowMasterCatalog (maskGeneratedRowDataFamily m gap₀) := by
    have h := originalRowMasterCatalog_inclusion (maskGeneratedRowDataFamily m gap) z _ hden
    rw [maskGeneratedMasterCatalog_gap_independent m gap gap₀] at h
    exact h
  have hP : ∀ q ∈ P, q ≠ 0 := maskRenamedLocalCatalog_nonzero m gap z
  have hpolP : pol ∈ P := Finset.mem_image.mpr ⟨_, hden, rfl⟩
  let anchor := targetRootAnchor gap z
  let q : Fin (maskRowCountBound m + 1) :=
    ⟨targetPredictionOrder gap z, Nat.lt_succ_of_le (maskGenerated_additive_dimension_le m gap z)⟩
  have hx := hshort anchor γ q pol hpol P hP hpolP
  have hd := maskOriginalSubset_detection_before_master gap a ha (fun _ => C)
    (fun _ => hCrange) J hJ hg ht hε
  have hb := maskEndpointTargetCube_abs_le_twice_primeGood_shortCube gap (fun _ => C) z J
  filter_upwards [hx, hU hd, hU hb, hH, htarget] with w hw hdet hbw hHw htw
  apply hdet z (H w) (b w) hHw
  have hlocal : expectation (conditionMass
      (primeIndependentMass (maskGeneratedRowDataFamily m gap z).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
      (primeSampleGood ((maskGeneratedRowDataFamily m gap z).rows.catalog
        (maskGeneratedRowDataFamily m gap z).target))) (fun x =>
      |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
        ((maskGeneratedMaster m gap).gap w (gap w).val)
        ((maskGeneratedMaster m gap).cutoff w (C.pivot anchor))
        (targetPredictionOrder gap z) J (targetPredictionPolynomial gap z)
        (fun y => f (C.tail anchor) (C.pivot anchor) γ w y -
          model (principalTailPositions e (C.tail anchor)) (p anchor) γ w y) x|) ≤
        maskUniformDetectionTolerance m ε / 2 := by
    rw [maskLocal_primeGood_shortCube_eq_renamed, hm, hgapval]
    simpa only [hp anchor, dyadicPoolTupleMass, primeIndependentMass, P, pol, q, l] using hw.le
  have hcube := hbw (H w (maskSourceNonemptySupport m z))
  rw [htw] at hcube
  rw [htw]
  dsimp only [anchor] at hlocal
  linarith

end Hindman168
