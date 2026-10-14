import Hindman168.RoughVectorVariableRenaming
import Hindman168.ScalarVariableEquiv
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! ACTUAL original canonical Haar discrepancy on SAME native datum and
SAME original cube samples commutes with genuine finite variable equivalence. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_polynomial_variable_equiv_sample {s : ℕ} {σ τ : Type*}
    (D : NativeNilmanifoldData.{u} s) (e : σ ≃ τ) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    nativeMvPolynomialOrbit D (roughVectorMvRename e p) (scalarVariableAssignmentEquiv e ℤ x) =
      nativeMvPolynomialOrbit D p x := by
  unfold nativeMvPolynomialOrbit
  rw [rough_vector_rename_eval]
  simp only [Function.comp_def,scalar_variable_equiv_apply,Equiv.symm_apply_apply]

theorem native_polynomial_variable_equiv_cube_discrepancy {s : ℕ} {σ τ : Type*} [Fintype σ] [Fintype τ]
    (D : NativeNilmanifoldData.{u} s) (e : σ ≃ τ) (p : RoughVectorMvPolynomial σ D.E) (N : ℕ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube τ N)
        (nativeMvPolynomialOrbit D (roughVectorMvRename e p)) H =
      nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H
  change finiteComplexSetMean (scalarMvIntegerCube τ N)
    (fun x => H (nativeMvPolynomialOrbit D (roughVectorMvRename e p) x)) -
    (∫ q, H q ∂nativeNilmanifoldQuotientProbability D) =
    finiteComplexSetMean (scalarMvIntegerCube σ N) (fun x => H (nativeMvPolynomialOrbit D p x)) -
    (∫ q, H q ∂nativeNilmanifoldQuotientProbability D)
  rw [scalar_variable_equiv_cube_mean e N]
  simp only [native_polynomial_variable_equiv_sample]

end Hindman168
