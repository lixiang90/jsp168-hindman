import Hindman168.ScalarUnitCubeMean
import Hindman168.NativeNilmanifoldFiniteDiscrepancy
import Hindman168.NativeCentralPolynomialProjection

/-! Exact equality of actual native canonical discrepancies for Unit cubes
and the same univariate interval samples, including empty sample sets. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_unit_cube_polynomial_discrepancy {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (N : ℕ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit N) (nativeMvPolynomialOrbit D p) H =
      nativeNilmanifoldFiniteDiscrepancy D (Finset.Ico 0 (N : ℤ))
        (fun n => nativeMvPolynomialOrbit D p (fun _ => n)) H := by
  intro H
  change finiteComplexSetMean (scalarMvIntegerCube Unit N) (fun x => H (nativeMvPolynomialOrbit D p x)) - _ =
    finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n => H (nativeMvPolynomialOrbit D p (fun _ => n))) - _
  rw [scalar_unit_integer_cube_mean]

end Hindman168
