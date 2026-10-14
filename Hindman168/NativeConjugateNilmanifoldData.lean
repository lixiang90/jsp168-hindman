import Hindman168.NativeNilmanifoldData
import Hindman168.RoughConjugateRightCosetMetric

/-! TRUE conjugated lattice native data retains the ORIGINAL model/group.
Actual compatible quotient metric is transported through the right-coset
homeomorphism, with all discrete/compact/quotient-map fields PROVED. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeConjugateNilmanifoldData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) : NativeNilmanifoldData.{u} s := by
  letI := roughConjugateSubgroup_discrete D.Γ ρ
  letI := roughConjugateSubgroup_quotient_compact D.Γ ρ
  letI : MetricSpace (D.G ⧸ D.Γ) := D.metric
  exact {
    E := D.E
    H := D.H
    I := D.I
    G := D.G
    step_le := D.step_le
    Γ := roughConjugateSubgroup D.Γ ρ
    metric := roughConjugateRightCosetMetric D.Γ ρ
    metric_quotientMap := rough_conjugate_right_coset_metric_quotientMap D.Γ ρ D.metric_quotientMap }

theorem native_conjugate_nilmanifold_lattice {s : ℕ} (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    (nativeConjugateNilmanifoldData D ρ).Γ=roughConjugateSubgroup D.Γ ρ := rfl

theorem native_conjugate_nilmanifold_metric {s : ℕ} (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI : MetricSpace (D.G ⧸ D.Γ) := D.metric
    (nativeConjugateNilmanifoldData D ρ).metric=roughConjugateRightCosetMetric D.Γ ρ := rfl

end Hindman168
