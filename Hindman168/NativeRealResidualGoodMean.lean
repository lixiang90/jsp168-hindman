import Hindman168.NativeRealResidualObservableApproximation

/-! Complement of the ORIGINAL non-strict test-family event gives a strict
bound on the SAME fine/coarse normalized means. Empty means are algebraic;
no probability or positive normalization is inferred from an empty set. -/
namespace Hindman168
open FiniteMass
universe u

theorem native_real_residual_good_integer_mean {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Z c C η : ℝ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (H : Set C(D.G ⧸ D.Γ,ℂ)) (F : C(D.G ⧸ D.Γ,ℂ)), F ∈ H →
    ¬RoughNativeRealResidualTestFamilyLargeIndex D Q a q z t Z c C η H →
    ∀ (lo hi b : κ → ℤ),
    (∀ j, c*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi j-(a j : ℝ))/(q : ℝ)| ≤ C*Z) →
    (∀ j, Int.ModEq q (a j) (b j)) →
    ‖complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi b (q*t : ℕ)))
      (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi a q))
      (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖ < η := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H F hF hgood lo hi b hgeom hcompatible
  apply lt_of_not_ge
  intro hlarge
  apply hgood
  refine ⟨(fun j => (lo j : ℝ)),(fun j => (hi j : ℝ)),b,F,hF,hgeom,hcompatible,?_⟩
  simpa only [Int.ceil_intCast] using hlarge

end Hindman168
