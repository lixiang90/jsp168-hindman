import Hindman168.NativeRationalLinePolynomial
import Hindman168.FiniteComplexIntegerRangeMean
import Hindman168.FiniteComplexDenseMean

/-! ACTUAL native short-line cube discrepancy equals the SAME original
sampled line centered by TRUE canonical Haar mean. Positivity is retained
where subtracting the constant inside a mean requires a nonempty sample. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_line_discrepancy_range {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (x : κ → ℤ) (q : κ → ℕ) (T : ℕ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit T)
        (nativeMvPolynomialOrbit D (nativeRationalLinePolynomial D p x q)) F =
      finiteComplexSetMean (Finset.range T)
        (fun n => F (nativeMvPolynomialOrbit D p (fun j => x j+(q j : ℤ)*(n : ℤ))))-
        ∫ z, F z ∂nativeNilmanifoldQuotientProbability D := by
  intro F
  change finiteComplexSetMean _ _-_= _
  rw [scalar_unit_integer_cube_nat_mean]
  simp_rw [native_rational_line_polynomial_orbit]

theorem native_rational_line_discrepancy_centered {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (x : κ → ℤ) (q : κ → ℕ) (T : ℕ) (hT : 0 < T) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit T)
        (nativeMvPolynomialOrbit D (nativeRationalLinePolynomial D p x q)) F =
      finiteComplexSetMean (Finset.range T)
        (fun n => F (nativeMvPolynomialOrbit D p (fun j => x j+(q j : ℤ)*(n : ℤ)))-
          ∫ z, F z ∂nativeNilmanifoldQuotientProbability D) := by
  intro F
  rw [native_rational_line_discrepancy_range,finiteComplexSetMean_sub_const _
    (Finset.nonempty_range_iff.mpr hT.ne')]

end Hindman168
