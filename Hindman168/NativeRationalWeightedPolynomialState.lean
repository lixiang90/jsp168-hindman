import Hindman168.NativeRationalCompactReducedPolynomial

/-! Actual states contain actual native data/filtration/coefficient polynomial
and PROVED weights/ordinary degree. The true compact reduction constructs the
successor, rather than postulating a degree-drop or orbit-inverse interface. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

abbrev NativeRationalWeightedPolynomialState (s ℓ : ℕ) :=
  Σ D : NativeNilmanifoldData.{u} s, Σ F : NativeRationalLieFiltration D ℓ,
    {p : RoughVectorMvPolynomial Unit D.E // RoughVectorMvWeightedDegree F.layer p 0 ∧ RoughVectorMvDegreeLE p ℓ}

noncomputable def nativeRationalWeightedPolynomialInitial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    NativeRationalWeightedPolynomialState.{u} s ℓ :=
  ⟨D,F,roughVectorMvZeroTrim p,rough_vector_zero_trim_weighted F.layer hp,
    by simpa only [Nat.sub_zero] using rough_vector_zero_trim_degree F.layer F.antitone hp F.terminal⟩

theorem native_rational_weighted_polynomial_initial_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeRationalWeightedPolynomialInitial D F p hp).2.2.val x =
      roughVectorMvEval (E := D.E) p x :=
  rough_vector_zero_trim_eval p x

theorem native_rational_weighted_polynomial_initial_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (x : Unit → ℤ) :
    nativeMvPolynomialOrbit D (nativeRationalWeightedPolynomialInitial D F p hp).2.2.val x =
      nativeMvPolynomialOrbit D p x := by
  unfold nativeMvPolynomialOrbit
  rw [native_rational_weighted_polynomial_initial_eval]

noncomputable def nativeRationalWeightedPolynomialStep {s ℓ : ℕ}
    (S : NativeRationalWeightedPolynomialState.{u} s ℓ) (h : ℤ) :
    NativeRationalWeightedPolynomialState.{u} s (ℓ-1) :=
  ⟨nativeRationalDegreeReducedData S.1 S.2.1,nativeDegreeReducedRationalLieFiltration S.1 S.2.1,
    nativeRationalCompactReducedPolynomial S.1 S.2.1 S.2.2.val S.2.2.property.1 h,
    native_rational_compact_reduced_polynomial_weighted S.1 S.2.1 S.2.2.val S.2.2.property.1 h,
    native_rational_compact_reduced_polynomial_degree S.1 S.2.1 S.2.2.val S.2.2.property.1 h⟩

theorem native_rational_weighted_polynomial_step_data {s ℓ : ℕ}
    (S : NativeRationalWeightedPolynomialState.{u} s ℓ) (h : ℤ) :
    (nativeRationalWeightedPolynomialStep S h).1 = nativeRationalDegreeReducedData S.1 S.2.1 := rfl

theorem native_rational_weighted_polynomial_step_sample {s ℓ : ℕ}
    (S : NativeRationalWeightedPolynomialState.{u} s ℓ) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRationalWeightedPolynomialStep S h).1
      (nativeRationalWeightedPolynomialStep S h).2.2.val (fun _ => n) =
    nativeRationalTerminalFactorMap (nativeRationalRelativeData S.1 S.2.1 1) (nativeRelativeRationalLieFiltration S.1 S.2.1)
      ((nativeRationalCompactNormalizedIntegerPair S.1 S.2.1 S.2.2.val S.2.2.property.1 h n) :
        (nativeRationalRelativeData S.1 S.2.1 1).G ⧸ (nativeRationalRelativeData S.1 S.2.1 1).Γ) :=
  native_rational_compact_reduced_polynomial_sample S.1 S.2.1 S.2.2.val S.2.2.property.1 h n

theorem native_rational_weighted_polynomial_initial_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (f : D.E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection f (nativeRationalWeightedPolynomialInitial D F p hp).2.2.val =
      roughVectorMvProjection f p := rough_vector_zero_trim_projection f p

end Hindman168
