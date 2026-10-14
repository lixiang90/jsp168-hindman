import Hindman168.NativeRealPeriodCorrelation
import Hindman168.CompleteCellNilOrbitRebase

namespace Hindman168
open scoped Classical
open NNReal
universe u

/-- Transport a bounded native correlator on K periods of an actual
integer residue cell to its original globally anchored real piece orbit.
The original native manifold and observable bounds are retained. -/
theorem native_complete_cell_correlation_transfer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (k : ℤ) (M q K : ℕ)
    [NeZero q] (hM : 0 < M) (hK : 0 < K) (r : Fin M) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (f : ℤ → ℝ) (obs : C(D.G ⧸ D.Γ, ℂ)) (g x : D.G) (B : ℝ) (Lip : ℝ≥0) (δ : ℝ),
      (∀ z, ‖obs z‖ ≤ B) → LipschitzWith Lip obs →
      δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
        (f (k * (M * q : ℕ) + r.val + (M : ℤ) * (n.val : ZMod q).val) : ℂ) *
          obs (g ^ (n.val : ℤ) * x))‖ →
      ∃ (j : Fin K) (x' : D.G) (η : ℂ) (obs' : C(D.G ⧸ D.Γ, ℝ)),
        x' = g ^ (-(k * q)) * (g ^ ((j.val * q : ℕ) : ℤ) * x) ∧
        ‖η‖ = 1 ∧ obs' = phaseRealObservable η obs ∧
        (∀ z, |obs' z| ≤ B) ∧ LipschitzWith Lip obs' ∧
        δ ≤ finiteHaarMean (fun t : Fin q => f (completeResidueCellPoint k M q r t) *
          obs' (pieceLinearOrbit D.Γ M (fun _ : Unit => g) (fun _ => x')
            () (completeResidueCellPoint k M q r t))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro f obs g x B Lip δ hB hLip hδ
  let v := fun z : ZMod q => f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val)
  obtain ⟨j, x₀, η, obs', hx₀, hη, he, hB', hLip', hcorr⟩ :=
    native_real_period_correlation_extract D K q hK v obs g x B Lip δ hB hLip hδ
  refine ⟨j, g ^ (-(k * q)) * x₀, η, obs', by rw [hx₀], hη, he, hB', hLip', ?_⟩
  rw [completeResidueCell_nil_correlation_rebase D.Γ k M q hM r f obs' g x₀]
  have hv (t : Fin q) : v (t.val : ZMod q) = f (completeResidueCellPoint k M q r t) := by
    dsimp only [v, completeResidueCellPoint]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt t.isLt]
  simpa only [hv] using hcorr

end Hindman168
