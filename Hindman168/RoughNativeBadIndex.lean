import Hindman168.NativeNilmanifoldData
import Hindman168.AlignmentBoxMeans
import Hindman168.FiniteMass

namespace Hindman168
open scoped Classical
universe u

/-- An actual discrepant pair of nonempty box samples on a specified native
quotient. The observable and box may depend on the progression index. -/
def RoughNativeBadIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (lo hi v : κ → ℤ) (F : (D.G ⧸ D.Γ) → ℝ),
    LipschitzWith L F ∧ (∀ x, |F x| ≤ B) ∧
    (∀ j, c*Z ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*Z ∧
      |(lo j : ℝ)| ≤ C*Z ∧ |(hi j : ℝ)| ≤ C*Z) ∧
    0 < (alignmentBoxClass lo hi v t).card ∧
    0 < (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))).card ∧
    η < |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      FiniteMass.expectation (FiniteMass.uniformFinsetMass
        (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))|

theorem rough_native_bad_index_mono {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    {z t : ℕ} {Z c C C' : ℝ} {L : NNReal} {B η : ℝ}
    (hZ : 0 ≤ Z) (hC : C ≤ C')
    (h : RoughNativeBadIndex D Q z t Z c C L B η) :
    RoughNativeBadIndex D Q z t Z c C' L B η := by
  obtain ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, hbad⟩ := h
  refine ⟨lo, hi, v, F, hL, hB, ?_, hstep, hfull, hbad⟩
  intro j
  have hh := mul_le_mul_of_nonneg_right hC hZ
  exact ⟨(hbox j).1, (hbox j).2.1.trans hh,
    (hbox j).2.2.1.trans hh, (hbox j).2.2.2.trans hh⟩

theorem rough_native_bad_index_reparametrize {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a b z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeBadIndex D Q (a+b*z) t Z c C L B η) :
    RoughNativeBadIndex D (fun x => Q
      (Option.elim · ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j))))
      z t Z c C L B η := by
  obtain ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, hbad⟩ := h
  refine ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, ?_⟩
  simpa only [Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_mul] using hbad

end Hindman168
