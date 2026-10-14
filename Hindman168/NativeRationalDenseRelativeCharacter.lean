import Hindman168.NativeRationalDenseFourierDerivatives
import Hindman168.NativeRationalRelativeCoefficientScale
import Hindman168.FiniteDenseWitnessSelection

/-! Genuine common relative character on a positive density of actual shifts.
All geometry, grids, density, norm and original-scale coefficient budgets
precede every source polynomial, observation and sample length. This remains
conditional only on the FULL actual lower-degree inverse. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_dense_relative_character {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A B ρ : ℝ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧
      ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), 0 < N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        ∃ χ ∈ C,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
          ∃ U : Finset ℕ, U.Nonempty ∧ ρ*(N : ℝ) ≤ U.card ∧
            ∀ h ∈ U, 0 < h ∧ h < N ∧ δ^2/8*(N : ℝ) ≤ (N-h : ℕ) ∧
              NativeRationalRelativeCoefficientBounds D L p hp h χ N B := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let τ : ℝ := δ^2/8
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by dsimp [τ]; nlinarith
  obtain ⟨A,hA,hInv⟩ := native_rational_nonzero_relative_inverse D L hdeg hInverse k hk τ hτ
  let C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :=
    (roughNativeHorizontalCharacterGrid (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ A).image LinearMap.toContinuousLinearMap
  let B : ℝ := A*(τ⁻¹)^ℓ
  let ρ : ℝ := τ/((C.card : ℝ)+1)
  have hDen : 0 < (C.card : ℝ)+1 := by positivity
  refine ⟨A,B,ρ,hA,by dsimp [B]; positivity,by dsimp [ρ]; positivity,C,?_⟩
  intro p hp N hN F hF hlarge hmean
  obtain ⟨T,hT,hDer⟩ := native_rational_dense_fourier_derivatives D L k δ hδ p N hN F hF hlarge hmean
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    have hpN : (0 : ℝ) < N := by exact_mod_cast hN
    have hpos : (0 : ℝ) < T.card := (mul_pos hτ hpN).trans_le hT
    exact_mod_cast hpos
  let P (h : ℕ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : Prop :=
    RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
      NativeRationalRelativeCoefficientBounds D L p hp h χ N B
  have hw : ∀ h ∈ T, ∃ χ ∈ C, P h χ := by
    intro h hh
    obtain ⟨_,_,hrem,hlen,hsignal⟩ := hDer h hh
    obtain ⟨χ,hHor,hNorm,hGrid,hCoeff,hBin⟩ := hInv p hp h (N-h) hrem F hF hsignal
    refine ⟨χ,?_,hHor,hNorm,?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨χ.toLinearMap,hGrid,?_⟩
      ext v
      rfl
    · exact native_rational_relative_coefficient_scale D L p hp h χ N (N-h) τ A
        hτ hτ1 hA.le hlen ⟨fun J hJ _ => hCoeff J hJ,fun J hJ _ => hBin J hJ⟩
  obtain ⟨χ,hχ,U,hUT,hUne,hcard,hcommon⟩ := finite_dense_witness_selection T hTne C P hw
  obtain ⟨h,hU⟩ := hUne
  obtain ⟨hHor,hNorm,_⟩ := hcommon h hU
  refine ⟨χ,hχ,hHor,hNorm,U,⟨h,hU⟩,?_,?_⟩
  · have hbound : τ*(N : ℝ) ≤ ((C.card : ℝ)+1)*(U.card : ℝ) :=
      hT.trans (hcard.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) U.card]))
    dsimp only [ρ]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hDen).mpr (by simpa only [mul_comm] using hbound)
  · intro h hh
    obtain ⟨hpos,hlt,_,hlen,_⟩ := hDer h (hUT hh)
    exact ⟨hpos,hlt,hlen,(hcommon h hh).2.2⟩

end Hindman168
