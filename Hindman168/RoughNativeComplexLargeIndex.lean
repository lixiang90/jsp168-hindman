import Hindman168.RoughNativeComplexBadIndex

/-! The manuscript's non-strict complex discrepancy event, on genuine
nonempty original samples. Reduction preserves every box and residue witness. -/
namespace Hindman168
open scoped Classical
universe u

def RoughNativeComplexLargeIndex {κ : Type*} [Fintype κ] {s : ℕ}
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
    η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
        (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖

theorem rough_native_complex_large_index_real {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) (hη : 0 < η)
    (h : RoughNativeComplexLargeIndex D Q z t Z c C L B η) :
    RoughNativeBadIndex D Q z t Z c C L B (η/4) := by
  obtain ⟨lo,hi,v,F,hL,hB,hbox,hstep,hfull,hlarge⟩ := h
  have hbad : RoughNativeComplexBadIndex D Q z t Z c C L B (η/2) :=
    ⟨lo,hi,v,F,hL,hB,hbox,hstep,hfull,by linarith⟩
  have hreal := rough_native_complex_bad_index_real D Q z t Z c C L B (η/2) hbad
  simpa only [div_div,show (2 : ℝ)*2=4 from by norm_num] using hreal

end Hindman168
