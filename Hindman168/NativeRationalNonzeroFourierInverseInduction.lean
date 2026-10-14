import Hindman168.NativeRationalDenseChildSignal
import Hindman168.NativeRationalFiniteCharacterInverseInduction

/-! ALL actual fixed nonzero terminal-frequency branches now give full
ORIGINAL nonzero character/grid/BOTH coefficient tables for large N, from
genuine lower-degree and strictly smaller-nonlinearity IH. No unconditional
higher-degree inverse is asserted. Thresholds precede every raw source. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonzero_fourier_inverse_induction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hLower : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ Q T : ℕ, 0 < Q ∧ 0 < T ∧
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (_hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        ∃ κ : D.E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap ∧ ‖κ‖ ≤ (Q : ℝ) ∧
          κ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
          (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
            (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
              (roughVectorMvProjection κ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
          ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
            (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,Q0,S,T0,_hA,hQ0,_hS,_hT0,_ρ,_hρ,C,B,hB,θ,hθ,hBudgets,hData⟩ :=
    native_rational_dense_child_signal D L hdeg hLower k hk δ hδ hδ1
  obtain ⟨Q1,hQ1,hOrig⟩ := native_rational_finite_character_inverse_induction D L hdeg hIH k
    (A : ℝ) δ S B θ hB hθ (Nat.cast_nonneg A) C hBudgets
  let Q := max Q0 Q1
  let T := T0+B+1
  have hQ : 0 < Q := hQ0.trans_le (le_max_left _ _)
  have hT : 0 < T := by dsimp only [T]; omega
  have hBudget0 : (Q0 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_max_left Q0 Q1
  have hBudget1 : (Q1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_max_right Q0 Q1
  refine ⟨Q,T,hQ,hT,?_⟩
  intro p hp N hTN F hF hLarge hSignal
  have hT0N : T0 ≤ N := (show T0 ≤ T by dsimp only [T]; omega).trans hTN
  have hBN : B ≤ N := (show B ≤ T by dsimp only [T]; omega).trans hTN
  rcases hData p hp N hT0N F hF hLarge hSignal with hOriginal | hRemaining
  · obtain ⟨κ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hOriginal
    have hn := hNorm.trans hBudget0
    exact ⟨κ,hHor,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q : ℝ) (Nat.cast_nonneg Q) κ hn hHor,
      fun I hI => (hMono I hI).trans hBudget0,fun I hI => (hBin I hI).trans hBudget0⟩
  · obtain ⟨χ,hχC,hHor,_hNorm,M,hM,hMS,hQM,_hQB,_hPM,_hPB,_hEval,_b,_hb,hDiff,_hZero,hPair,_hRest⟩ := hRemaining
    have hGood : NativeRationalNonlinearityCharacterGood D L χ := ⟨hHor,hPair,hDiff⟩
    obtain ⟨κ,hHorNew,hNorm,_hGrid,hMono,hBin⟩ :=
      hOrig χ hχC hGood M hM hMS p hp N hBN hQM F hF hSignal
    have hn := hNorm.trans hBudget1
    exact ⟨κ,hHorNew,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q : ℝ) (Nat.cast_nonneg Q) κ hn hHorNew,
      fun I hI => (hMono I hI).trans hBudget1,fun I hI => (hBin I hI).trans hBudget1⟩

end Hindman168
