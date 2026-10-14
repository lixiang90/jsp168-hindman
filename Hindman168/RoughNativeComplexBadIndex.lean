import Hindman168.RoughNativeBadIndex
import Hindman168.ComplexRealObservable

namespace Hindman168
open scoped Classical
universe u

def RoughNativeComplexBadIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (lo hi v : κ → ℤ) (F : (D.G ⧸ D.Γ) → ℂ),
    LipschitzWith L F ∧ (∀ x, ‖F x‖ ≤ B) ∧
    (∀ j, c*Z ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*Z ∧
      |(lo j : ℝ)| ≤ C*Z ∧ |(hi j : ℝ)| ≤ C*Z) ∧
    0 < (alignmentBoxClass lo hi v t).card ∧
    0 < (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))).card ∧
    η < ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
        (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖

theorem rough_native_complex_bad_index_real {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeComplexBadIndex D Q z t Z c C L B η) :
    RoughNativeBadIndex D Q z t Z c C L B (η/2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, hbad⟩ := h
  obtain ⟨G, hGL, hGB, hdisc⟩ := complex_discrepancy_real_observable
    (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
    (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
    (fun y => QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ)))))
    F L B hL hB
  refine ⟨lo, hi, v, G, hGL, hGB, hbox, hstep, hfull, ?_⟩
  exact lt_of_lt_of_le (by linarith [hbad]) hdisc

end Hindman168
