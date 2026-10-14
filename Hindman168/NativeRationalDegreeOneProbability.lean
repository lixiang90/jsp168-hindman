import Hindman168.NativeRationalDegreeOneData
import Hindman168.NativeNilmanifoldFiniteDiscrepancy
import Hindman168.NativeCentralPolynomialProjection

/-! Reclassification of the PROVED abelian bound preserves the ACTUAL
original canonical Haar, original quotient probability, metric and samples.
These identities are literal original data identities, not an assumed measure. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_degree_one_original_group_haar {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    nativeNilmanifoldGroupHaar (nativeRationalDegreeOneData D F) = nativeNilmanifoldGroupHaar D := rfl

theorem native_rational_degree_one_original_fundamental_domain {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    nativeNilmanifoldFundamentalDomain (nativeRationalDegreeOneData D F) = nativeNilmanifoldFundamentalDomain D := rfl

theorem native_rational_degree_one_original_quotient_probability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    nativeNilmanifoldQuotientProbability (nativeRationalDegreeOneData D F) = nativeNilmanifoldQuotientProbability D := rfl

theorem native_rational_degree_one_original_polynomial_sample {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1)
    (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    nativeMvPolynomialOrbit (nativeRationalDegreeOneData D F) p x = nativeMvPolynomialOrbit D p x := rfl

theorem native_rational_degree_one_original_finite_discrepancy {s : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ), nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeOneData D F) a f H =
      nativeNilmanifoldFiniteDiscrepancy D a f H := by
  intro H
  rfl

end Hindman168
