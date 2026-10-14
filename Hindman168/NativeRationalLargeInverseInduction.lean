import Hindman168.NativeRationalNonzeroFourierInverseInduction
import Hindman168.NativeRationalInverseBoundedAlternative
import Hindman168.NativeUnitCubePolynomialDiscrepancy

/-! Actual zero mode and EVERY nonzero frequency in the original finite
Fourier pool compose to the FULL native inverse conclusion for large N,
from genuine degree/nonlinearity IH. All thresholds precede raw sources.
Original small-N cases and unconditional induction remain to be proved. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeRationalTerminalFrequencyBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (δ : ℝ) (Q T : ℕ) : Prop :=
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (p : RoughVectorMvPolynomial Unit D.E), RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ N : ℕ, T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
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
            (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)

theorem native_rational_large_inverse_induction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hLower : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (hZero : NativeRationalWeightedInverseStatement (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) Unit)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ Q T : ℕ, 0 < Q ∧ 0 < T ∧
      ∀ p : RoughVectorMvPolynomial Unit D.E, RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ N : ℕ, T ≤ N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit N) (nativeMvPolynomialOrbit D p) H‖ →
      ∃ κ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap ∧ ‖κ‖ ≤ (Q : ℝ) ∧
        κ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
        (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection κ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  obtain ⟨η,hη,hη1,Q0,hQ0,S,_hS,hSelect⟩ := native_rational_inverse_bounded_alternative D L Unit hZero δ hδ
  let I := {k // k ∈ S}
  have hEach (i : I) : ∃ Q T : ℕ, 0 < Q ∧ 0 < T ∧
      (i.val ≠ 0 → NativeRationalTerminalFrequencyBudget D L i.val η Q T) := by
    by_cases hk : i.val ≠ 0
    · obtain ⟨Q,T,hQ,hT,hData⟩ := native_rational_nonzero_fourier_inverse_induction D L hdeg hLower hIH
        i.val hk η hη hη1
      exact ⟨Q,T,hQ,hT,fun _ => hData⟩
    · exact ⟨1,1,by omega,by omega,fun h => (hk h).elim⟩
  choose q t hq ht hData using hEach
  let Q := Q0+1+∑ i, q i
  let T := 1+(∑ i, t i)+⌈4/(η^2)⌉₊
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hT : 0 < T := by dsimp only [T]; omega
  have hQ0Q : Q0 ≤ Q := by dsimp only [Q]; omega
  have hQiQ (i : I) : q i ≤ Q :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by dsimp only [Q]; omega)
  have hTiT (i : I) : t i ≤ T :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by dsimp only [T]; omega)
  refine ⟨Q,T,hQ,hT,?_⟩
  intro p hp N hTN H hH hBad
  have hN : 0 < N := hT.trans_le hTN
  rcases hSelect p hp N hN H hH hBad with hOriginal | hFrequency
  · obtain ⟨κ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hOriginal
    have hBudget : (Q0 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ0Q
    have hn := hNorm.trans hBudget
    exact ⟨κ,hHor,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q : ℝ) (Nat.cast_nonneg Q) κ hn hHor,
      fun J hJ => (hMono J hJ).trans hBudget,fun J hJ => (hBin J hJ).trans hBudget⟩
  · obtain ⟨k,hkS,hk,hSignal⟩ := hFrequency
    let i : I := ⟨k,hkS⟩
    have hThreshold : 4/(η^2) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈4/(η^2)⌉₊ ≤ T by dsimp only [T]; omega).trans hTN)
    have hLarge : 4 ≤ η^2*(N : ℝ) := by
      have h := (div_le_iff₀ (by positivity : 0 < η^2)).mp hThreshold
      simpa only [mul_comm] using h
    have hInterval : η ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
        nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n)))‖ := by
      rw [scalar_unit_integer_cube_mean] at hSignal
      exact hSignal
    obtain ⟨κ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hData i hk p hp N ((hTiT i).trans hTN) H hH hLarge hInterval
    have hBudget : (q i : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQiQ i
    have hn := hNorm.trans hBudget
    exact ⟨κ,hHor,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q : ℝ) (Nat.cast_nonneg Q) κ hn hHor,
      fun J hJ => (hMono J hJ).trans hBudget,fun J hJ => (hBin J hJ).trans hBudget⟩

end Hindman168
