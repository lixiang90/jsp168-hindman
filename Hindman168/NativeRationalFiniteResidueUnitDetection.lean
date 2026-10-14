import Hindman168.NativeConjugateFourierUnitDetection
import Hindman168.FinitePositiveThresholdMinimum

/-! ONE actual positive UNIT-detection threshold works for ALL positive
M<=S and finite rational representatives m<M*q, BEFORE all raw sources,
samples and frozen error coefficients. Actual compact scalar LEFT family
and TRUE conjugated native data are used. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u v
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_finite_residue_unit_detection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (y : D.E)
    (B δ : ℝ) (S q : ℕ) (hδ : 0 < δ) (hS : 0 < S) (hq : 0 < q) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧ ∀ M : ℕ, 0 < M → M ≤ S → ∀ m : ℕ, m < M*q →
      let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
      letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
      letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
        (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
      ∀ {α : Type v} (a : Finset α) (orbit : α → D.G ⧸ roughConjugateSubgroup D.Γ ρ)
        (c : ℝ), |c| ≤ B → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        δ ≤ ‖finiteComplexSetMean a (fun n => nativeConjugateFourierObservable D L k ρ
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (c • y)) F (orbit n))‖ →
        ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
          θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeConjugateNilmanifoldData D ρ) a orbit J‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let I := Fin S × Fin (S*q)
  letI : NeZero S := ⟨hS.ne'⟩
  letI : NeZero (S*q) := ⟨(Nat.mul_pos hS hq).ne'⟩
  let C := (fun t : ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (t • y)) '' Set.Icc (-B) B
  have hScalar : Continuous (fun t : ℝ => (t • y : D.E)) := continuous_id.smul continuous_const
  have hC : IsCompact C := isCompact_Icc.image
    ((nativeLieExponential_continuous (E := D.E) (I := D.I) (G := D.G)).comp hScalar)
  let ρf : I → D.G := fun i => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (((i.2.val : ℝ)/((i.1.val+1 : ℕ) : ℝ)) • y)
  have hEach (i : I) : ∃ θ : ℝ, 0 < θ ∧
      (letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ (ρf i)) := (nativeConjugateNilmanifoldData D (ρf i)).metric;
       letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ (ρf i)) :=
         (nativeConjugateNilmanifoldData D (ρf i)).metric.toUniformSpace.toTopologicalSpace;
       ∀ {α : Type v} (a : Finset α) (orbit : α → D.G ⧸ roughConjugateSubgroup D.Γ (ρf i))
         (c : ℝ), |c| ≤ B → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
         δ ≤ ‖finiteComplexSetMean a (fun n => nativeConjugateFourierObservable D L k (ρf i)
           (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (c • y)) F (orbit n))‖ →
         ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ (ρf i)),
           θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeConjugateNilmanifoldData D (ρf i)) a orbit J‖) := by
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ (ρf i)) := (nativeConjugateNilmanifoldData D (ρf i)).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ (ρf i)) :=
      (nativeConjugateNilmanifoldData D (ρf i)).metric.toUniformSpace.toTopologicalSpace
    obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_conjugate_fourier_unit_detection D L k hk (ρf i) C hC δ hδ
    refine ⟨θ,hθ,?_⟩
    intro α a orbit c hc F hF hMean
    obtain ⟨J,hJ,hLarge⟩ := hDetect a orbit _ ⟨c,abs_le.mp hc,rfl⟩ F hF hMean
    exact ⟨J,hP J hJ,hLarge⟩
  choose t ht hSignals using hEach
  obtain ⟨θ,hθ,hLe⟩ := finite_positive_threshold_minimum t ht
  refine ⟨θ,hθ,?_⟩
  intro M hM hMS m hm
  let i : I := (⟨M-1,by omega⟩,⟨m,hm.trans_le (Nat.mul_le_mul_right q hMS)⟩)
  have hMval : i.1.val+1=M := by dsimp only [i]; omega
  have hρi : ρf i=nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) := by
    dsimp only [ρf,i]
    have he : M-1+1=M := by omega
    rw [he]
  have hDetect := @hSignals i
  rw [hρi] at hDetect
  dsimp only
  intro α a orbit c hc F hF hMean
  obtain ⟨J,hJ,hLarge⟩ := @hDetect α a orbit c hc F hF hMean
  exact ⟨J,hJ,(hLe i).trans_lt hLarge⟩

end Hindman168
