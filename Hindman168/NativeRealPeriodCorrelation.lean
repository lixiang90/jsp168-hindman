import Hindman168.NilsequencePeriodCorrelation
import Hindman168.PhaseObservableCorrelation

namespace Hindman168
open scoped Classical
open NNReal
universe u

/-- A real cyclic input retains the interval correlation threshold on one
period of the original native nilmanifold, with the same observable bounds.
The only changes are its basepoint and a unit phase followed by real part. -/
theorem native_real_period_correlation_extract {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K q : ℕ) [NeZero q] (hK : 0 < K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (v : ZMod q → ℝ) (obs : C(D.G ⧸ D.Γ, ℂ)) (g x : D.G) (B : ℝ) (Lip : ℝ≥0) (δ : ℝ),
      (∀ z, ‖obs z‖ ≤ B) → LipschitzWith Lip obs →
      δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
        (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖ →
      ∃ (j : Fin K) (x' : D.G) (η : ℂ) (obs' : C(D.G ⧸ D.Γ, ℝ)),
        x' = g ^ ((j.val * q : ℕ) : ℤ) * x ∧ ‖η‖ = 1 ∧ obs' = phaseRealObservable η obs ∧
        (∀ z, |obs' z| ≤ B) ∧ LipschitzWith Lip obs' ∧
        δ ≤ finiteHaarMean (fun z : Fin q => v (z.val : ZMod q) * obs' (g ^ (z.val : ℤ) * x')) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro v obs g x B Lip δ hB hLip hδ
  obtain ⟨j, hj⟩ := linear_nilsequence_period_correlation_extract D.Γ K q hK
    (fun z => (v z : ℂ)) obs g x δ hδ
  let x' := g ^ ((j.val * q : ℕ) : ℤ) * x
  obtain ⟨η, hη, he⟩ := finite_real_correlation_phase_choice
    (fun z : Fin q => v (z.val : ZMod q)) (fun z => obs (g ^ (z.val : ℤ) * x'))
  refine ⟨j, x', η, phaseRealObservable η obs, rfl, hη, rfl,
    phaseRealObservable_abs_le η hη obs B hB, phaseRealObservable_lipschitz η hη obs Lip hLip, ?_⟩
  change δ ≤ finiteHaarMean (fun z : Fin q => v (z.val : ZMod q) *
    (η * obs (g ^ (z.val : ℤ) * x')).re)
  rw [he]
  exact hj

end Hindman168
