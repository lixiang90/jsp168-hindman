import Hindman168.NativeRationalSelectedRepresentatives
import Hindman168.NativeRationalWeightedNormalizations
import Hindman168.NativeRationalWeightedIntegerPair

/-! Actual coefficient-dependent normalization choices from ONE compact set
fixed before all source coefficients and integer shifts. All inputs are proved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalBasepointRepresentative {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) : D.G :=
  nativeRationalRepresentative D (nativeIntegerLogPolynomialSequence D p 0)

noncomputable def nativeRationalBasepointLatticePart {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) : D.Γ :=
  nativeRationalRepresentativeLatticePart D (nativeIntegerLogPolynomialSequence D p 0)

noncomputable def nativeRationalLinearLatticePart {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) : D.Γ :=
  nativeRationalRepresentativeLatticePart D
    (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p)) 1)

noncomputable def nativeRationalCompactNormalizedPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) : RoughVectorMvPolynomial Unit D.E :=
  nativeLinearStepPolynomial D (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p))
    (nativeRationalLinearLatticePart D p)

noncomputable def nativeRationalShiftRepresentative {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (h : ℤ) : D.G :=
  nativeRationalRepresentative D (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ^ h)

theorem native_rational_compact_basepoint_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p 0) =
      nativeRationalBasepointRepresentative D p * nativeRationalBasepointLatticePart D p := by
  have he := native_rational_representative_factorization D (nativeIntegerLogPolynomialSequence D p 0)
  have hz : (0 : Unit → ℝ) = (fun _ => 0) := rfl
  rw [hz]
  simpa only [nativeRationalBasepointRepresentative,nativeRationalBasepointLatticePart,
    nativeIntegerLogPolynomialSequence,Int.cast_zero] using he

theorem native_rational_compact_normalized_polynomial_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) :
    nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 =
      nativeRationalRepresentative D
        (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p)) 1) := by
  have he := native_rational_representative_factorization D
    (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p)) 1)
  have hx := native_linear_step_one_exponential D
    (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p))
    (nativeRationalRepresentative D
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p (nativeRationalBasepointRepresentative D p)) 1))
    (nativeRationalLinearLatticePart D p)
    (by simpa only [nativeRationalLinearLatticePart,nativeIntegerLogPolynomialSequence,Int.cast_one] using he)
  simpa only [nativeRationalCompactNormalizedPolynomial,nativeIntegerLogPolynomialSequence,Int.cast_one] using hx

theorem native_rational_compact_normalized_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvWeightedDegree F.layer (nativeRationalCompactNormalizedPolynomial D p) 0 :=
  native_rational_weighted_two_normalizations D F hp _ _

theorem native_rational_compact_normalized_polynomial_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) :
    roughVectorMvEval (E := D.E) (nativeRationalCompactNormalizedPolynomial D p) (fun _ => 0) = 0 :=
  native_two_normalizations_logarithmic_zero D p _ _

theorem native_rational_compact_normalized_polynomial_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvDegreeLE (nativeRationalCompactNormalizedPolynomial D p) ℓ :=
  native_rational_weighted_two_normalizations_degree D F hp _ _

theorem native_rational_compact_normalized_original_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (x : Unit → ℤ) :
    nativeRationalBasepointRepresentative D p •
      nativeMvPolynomialOrbit D (nativeRationalCompactNormalizedPolynomial D p) x = nativeMvPolynomialOrbit D p x :=
  native_two_normalizations_original_orbit D p _ (nativeRationalBasepointLatticePart D p)
    (nativeRationalLinearLatticePart D p) (native_rational_compact_basepoint_factorization D p) x

theorem native_rational_compact_shift_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (h : ℤ) :
    nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ^ h =
      nativeRationalShiftRepresentative D p h * nativeRationalRepresentativeLatticePart D
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ^ h) :=
  native_rational_representative_factorization D _

theorem native_rational_compact_normalization_uniform_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E) (h : ℤ),
      nativeRationalBasepointRepresentative D p ∈ nativeRationalRepresentativeSet D ∧
      nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ∈ nativeRationalRepresentativeSet D ∧
      nativeRationalShiftRepresentative D p h ∈ nativeRationalRepresentativeSet D ∧
      ‖nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)‖ ≤ B := by
  obtain ⟨B,hB,hBound⟩ := native_rational_representative_log_bound D
  refine ⟨B,hB,fun p h => ?_⟩
  have hm : nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ∈
      nativeRationalRepresentativeSet D := by
    rw [native_rational_compact_normalized_polynomial_one]
    exact native_rational_representative_mem D _
  exact ⟨native_rational_representative_mem D _,hm,native_rational_representative_mem D _,hBound _ hm⟩

end Hindman168
