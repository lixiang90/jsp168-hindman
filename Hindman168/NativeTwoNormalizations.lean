import Hindman168.NativeLinearStepFiltered
import Hindman168.NativeLinearStepSamples
import Hindman168.NativeLinearStepHorizontal
import Hindman168.NativeBasepointPolynomialSamples
import Hindman168.NativeBasepointHorizontalPolynomial

/-! Both actual Green--Tao normalizations on every ORIGINAL bounded-degree
univariate polynomial. Compact choices precede all coefficients and all
horizontal characters; exact original samples and original weights survive. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_two_normalizations_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r γ : D.G) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)
        (fun _ => 0)) = 1 := by
  rw [native_linear_step_zero_exponential]
  have he : (fun _ : Unit => (0 : ℝ)) = (0 : Unit → ℝ) := rfl
  rw [he,native_basepoint_polynomial_zero]
  exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)

theorem native_two_normalizations_original_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r : D.G)
    (γ₀ γ₁ : D.Γ)
    (h0 : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r*γ₀) (x : Unit → ℤ) :
    r • nativeMvPolynomialOrbit D (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ₁) x =
      nativeMvPolynomialOrbit D p x := by
  rw [native_linear_step_original_orbit]
  exact native_basepoint_polynomial_original_orbit D p r γ₀ h0 x

theorem native_two_normalizations_original_nonconstant_coefficients {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r : D.G) (γ : D.Γ)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (hInt : ∀ g : D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ))
    (J : Unit →₀ ℕ) (hJ : J ≠ 0) :
    ∃ z : ℤ, MvPolynomial.coeff J (roughVectorMvProjection f
      (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)) =
        MvPolynomial.coeff J (roughVectorMvProjection f p)+(z : ℝ) := by
  obtain ⟨z,hz⟩ := native_linear_step_horizontal_coefficient_integer_shift D
    (nativeBasepointPolynomial D p r) γ f hf hInt J
  rw [native_basepoint_horizontal_nonconstant_coeff D p r f hf J hJ] at hz
  exact ⟨z,hz⟩

theorem native_two_normalizations_fixed_compact_data {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    ∃ K : Set D.G, IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ a ∈ K, ‖nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a‖ ≤ B) ∧
      ∀ p : RoughVectorMvPolynomial Unit D.E, RoughVectorMvDegreeLE p d →
        ∃ r ∈ K, ∃ a ∈ K, ∃ γ₀ γ₁ : D.Γ,
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p 0) = r*γ₀ ∧
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun _ => 1)) = a*γ₁ ∧
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ₁)
              (fun _ => 1)) = a ∧
          RoughVectorMvDegreeLE (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ₁) (s*d) ∧
          RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
            (fun n : ℤ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ₁)
                (fun _ => (n : ℝ)))) := by
  obtain ⟨K,hK,hRep⟩ := native_exists_compact_coset_representatives D
  obtain ⟨b,hb⟩ := hK.bddAbove_image
    ((nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)).continuous.norm.continuousOn)
  refine ⟨K,hK,max b 0,le_max_right _ _,?_,?_⟩
  · intro a ha
    exact (hb (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _)
  · intro p hp
    obtain ⟨r,hr,γ₀,h0⟩ := hRep
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p 0))
    obtain ⟨a,ha,γ₁,h1⟩ := hRep (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun _ => 1)))
    have hw := native_basepoint_polynomial_weighted D d hd p hp r
    exact ⟨r,hr,a,ha,γ₀,γ₁,h0,h1,native_linear_step_one_exponential D _ a γ₁ h1,
      native_linear_step_polynomial_degree D d hd hw γ₁,
      native_linear_step_integer_polynomial_filtered D d hd hw γ₁⟩

end Hindman168
