import Hindman168.ComplexMeanObservableApproximation
import Hindman168.NativeRealResidualLargeEvent
import Hindman168.AlignmentJointMetricReadings

/-! Original continuous test-family residual events embed into the genuine
bounded Lipschitz event after one uniform approximation chosen before boxes,
residues, source and removed factor. Non-strict thresholds retain a margin. -/
namespace Hindman168
universe u
open FiniteMass

def RoughNativeRealResidualTestFamilyLargeIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Z c C η : ℝ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Set C(D.G ⧸ D.Γ,ℂ) → Prop := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H
  exact ∃ (lo hi : κ → ℝ) (b : κ → ℤ) (F : C(D.G ⧸ D.Γ,ℂ)),
    F ∈ H ∧
    (∀ j, c*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi j-(a j : ℝ))/(q : ℝ)| ≤ C*Z) ∧
    (∀ j, Int.ModEq q (a j) (b j)) ∧
    η ≤ ‖complexExpectation (uniformFinsetMass
      (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) b (q*t : ℕ)))
      (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      complexExpectation (uniformFinsetMass
      (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a q))
      (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖

theorem rough_native_real_residual_test_family_approximation {κ : Type*} [Fintype κ]
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Z c C η B : ℝ) (L : NNReal) (hη : 0 < η) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
    ∀ H : Set C(D.G ⧸ D.Γ,ℂ),
    (∀ F ∈ H, ∃ G : C(D.G ⧸ D.Γ,ℂ), LipschitzWith L G ∧
      (∀ y, ‖G y‖ ≤ B) ∧ ‖F-G‖ < η/4) →
    RoughNativeRealResidualTestFamilyLargeIndex D Q a q z t Z c C η H →
    RoughNativeRealResidualComplexLargeIndex D Q a q z t Z c C L B (η/2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
  intro H happrox hbad
  obtain ⟨lo,hi,b,F,hF,hgeom,hcompatible,hdiscrepancy⟩ := hbad
  obtain ⟨G,hL,hB,hclose⟩ := happrox F hF
  refine ⟨lo,hi,b,G,hL,hB,hgeom,hcompatible,?_⟩
  let S := alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) b (q*t : ℕ)
  let T := alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a q
  let o : (κ → ℤ) → D.G ⧸ D.Γ := fun y =>
    QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))
  exact complex_two_uniform_means_continuous_approximation (α := κ → ℤ)
    (X := D.G ⧸ D.Γ) S T o F G η hη hclose hdiscrepancy

theorem rough_native_real_residual_compact_family_bounds {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (η : ℝ) (hη : 0 < η) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
    ∀ H : Set C(D.G ⧸ D.Γ,ℂ), IsCompact H →
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
      ∀ F ∈ H, ∃ G : C(D.G ⧸ D.Γ,ℂ), LipschitzWith (Real.toNNReal L) G ∧
        (∀ y, ‖G y‖ ≤ B) ∧ ‖F-G‖ < η/4 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
  intro H hH
  obtain ⟨B,L,hB,hL,P,hP,hclose⟩ := compact_family_bounded_lipschitz_approximation
    (D.G ⧸ D.Γ) H hH (η/4) (by positivity)
  refine ⟨B,L,hB,hL,?_⟩
  intro F hF
  obtain ⟨G,hG,hclose⟩ := hclose F hF
  exact ⟨G,(hP G hG).2,(hP G hG).1,hclose⟩

end Hindman168
