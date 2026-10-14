import Hindman168.NativeRationalTerminalImageLayers
import Hindman168.NativeArbitraryLieFilteredPolynomial
import Hindman168.RoughVectorMvProjectionNaturality
import Hindman168.RoughVectorZeroTrim
import Hindman168.NativeCentralPolynomialProjection

/-! ACTUAL weighted native coefficient polynomials project to the ACTUAL
terminal quotient, retaining evaluations/scalar coefficients and obtaining
the genuine ordinary degree decrease after zero-vector-term removal. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalTerminalPolynomial {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) : RoughVectorMvPolynomial σ (nativeRationalTerminalQuotientData D F).E :=
  roughVectorMvLinearMap (nativeRationalTerminalModelProjection D F).toLinearMap p

theorem native_rational_terminal_polynomial_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial σ D.E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F.layer p k) :
    RoughVectorMvWeightedDegree (nativeTerminalRationalLieFiltration D F).layer
      (nativeRationalTerminalPolynomial D F p) k := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact Submodule.mem_map_of_mem (hp b hb)

theorem native_rational_terminal_polynomial_eval {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    roughVectorMvEval (nativeRationalTerminalPolynomial D F p) x =
      nativeRationalTerminalModelProjection D F (roughVectorMvEval (E := D.E) p x) :=
  roughVectorMvLinearMap_eval _ p x

theorem native_rational_terminal_polynomial_exponential {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    nativeLieExponential (E := (nativeRationalTerminalQuotientData D F).E)
      (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)
      (roughVectorMvEval (E := (nativeRationalTerminalQuotientData D F).E)
        (nativeRationalTerminalPolynomial D F p) x) =
      nativeRationalTerminalGroupProjection D F
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)) := by
  rw [native_rational_terminal_polynomial_eval]
  exact (native_rational_terminal_data_exponential D F (roughVectorMvEval (E := D.E) p x)).symm

theorem native_rational_terminal_polynomial_scalar {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (χ : (nativeRationalTerminalQuotientData D F).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection χ (nativeRationalTerminalPolynomial D F p) =
      roughVectorMvProjection (χ.comp (nativeRationalTerminalModelProjection D F).toLinearMap) p :=
  roughVectorMvProjection_linearMap _ _ p

theorem native_rational_terminal_polynomial_zero_trim_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial σ D.E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F.layer p k) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D F p)) ((ℓ-1)-k) :=
  rough_vector_zero_trim_degree (nativeTerminalRationalLieFiltration D F).layer
    (nativeTerminalRationalLieFiltration D F).antitone
    (native_rational_terminal_polynomial_weighted D F hp) (nativeTerminalRationalLieFiltration D F).terminal

theorem native_rational_terminal_polynomial_coefficients {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (χ : (nativeRationalTerminalQuotientData D F).E →ₗ[ℝ] ℝ)
    (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ (nativeRationalTerminalPolynomial D F p)) =
      MvPolynomial.coeff J (roughVectorMvProjection (χ.comp (nativeRationalTerminalModelProjection D F).toLinearMap) p) := by
  rw [native_rational_terminal_polynomial_scalar]

theorem native_rational_terminal_polynomial_real_filtered {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial σ D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughFilteredPolynomial (nativeRationalTerminalImageGroupLayer D F)
      (fun x : σ → ℝ => nativeLieExponential (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)
        (roughVectorMvEval (E := (nativeRationalTerminalQuotientData D F).E) (nativeRationalTerminalPolynomial D F p) x)) := by
  apply native_arbitrary_lie_polynomial_filtered (nativeRationalTerminalQuotientData D F)
    (nativeTerminalRationalLieFiltration D F).layer (nativeTerminalRationalLieFiltration D F).antitone
    (nativeTerminalRationalLieFiltration D F).bracket
  · intro i v hv
    apply (native_rational_terminal_image_logarithm_iff D F i _).mpr
    exact (congrArg (fun z : (nativeRationalTerminalQuotientData D F).E =>
      z ∈ nativeRationalTerminalImageLieLayer D F i)
      (nativeLieGlobalLogarithm_exponential (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G) v)).mpr hv
  · exact native_rational_terminal_polynomial_weighted D F hp

theorem native_rational_terminal_polynomial_integer_orbit {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    nativeRationalTerminalFactorMap D F (nativeMvPolynomialOrbit D p x) =
      nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D F) (nativeRationalTerminalPolynomial D F p) x := by
  unfold nativeMvPolynomialOrbit
  change ((nativeRationalTerminalGroupProjection D F
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun i => (x i : ℝ))))) :
        (nativeRationalTerminalQuotientData D F).G ⧸ (nativeRationalTerminalQuotientData D F).Γ) = _
  rw [native_rational_terminal_data_exponential,native_rational_terminal_polynomial_eval]

end Hindman168
