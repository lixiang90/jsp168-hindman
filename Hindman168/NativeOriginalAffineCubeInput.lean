import Hindman168.NativeOriginalBoundedCubeObstruction
import Hindman168.RoughVectorSpatialAffineProjection
import Hindman168.ScalarMvNaturalCubeTransport

namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Classical BigOperators Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- GENUINELY discharge the actual translated-cube binomial input used by
the retained real-box transfer. The original Q, joint polynomial and F remain. -/
theorem native_original_affine_cube_binomial_input
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (B : ℝ) (L : NNReal) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (p : RoughVectorMvPolynomial (Option (Fin n)) D.E), RoughVectorMvDegreeLE p d →
      (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ (z : ℝ) (b : Fin n → ℤ) (N : ℕ), 0 < N →
        ∀ F : C(D.G ⧸ D.Γ, ℂ), LipschitzWith L F → (∀ q, ‖F q‖ ≤ B) →
          η ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : Fin n => Finset.range N))
            (fun v => F (Q (fun i => i.elim z (fun j => ((b j+(v j : ℤ) : ℤ) : ℝ))) : D.G ⧸ D.Γ)) -
              ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ →
          ∃ χ : D.E →L[ℝ] ℝ, ‖χ‖ ≤ (M : ℝ) ∧
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ∃ (α : (Fin n → ℕ) → ℝ) (c0 : ℝ),
              roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
                (roughScalarSpatialProjection χ.toLinearMap p z) =
                  C c0+∑ J ∈ roughSpatialDegreeIndices (Fin n) d, C (α J)*roughMvBinomialPolynomial J ∧
              ∀ J ∈ roughSpatialDegreeIndices (Fin n) d,
                ‖(α J : UnitAddCircle)‖ ≤ (M : ℝ)*(N : ℝ)⁻¹^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M, hM, hinv⟩ := native_original_bounded_cube_obstruction D n d B L η hη
  refine ⟨M, hM, ?_⟩
  intro Q p hp hQ z b N hN F hF hB hbad
  let r := roughVectorMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
    (roughVectorMvParameterSpecialize z p)
  let R := fun x : Fin n → ℝ => Q (fun i => i.elim z (fun j => (b j : ℝ)+x j))
  have hr : RoughVectorMvDegreeLE r d := roughVectorMvAffineSubstitution_degree _ _
    (rough_vector_parameter_specialize_degree z hp)
  have hR : ∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (R x) = roughVectorMvEval r x := by
    intro x
    rw [roughVectorMvAffineSubstitution_eval, rough_vector_parameter_specialize_eval]
    simp only [one_mul]
    exact hQ _
  have hbad' : η ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
      (fun x => F (R (fun j => (x j : ℝ)) : D.G ⧸ D.Γ)) - ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ := by
    rw [scalar_mv_integer_cube_natural_mean]
    have hpi : @Fintype.piFinset (Fin n) (fun a b => Classical.propDecidable (a=b))
        (Fin.fintype n) (fun _ => ℕ) (fun _ => Finset.range N) =
        @Fintype.piFinset (Fin n) (instDecidableEqFin n) (Fin.fintype n)
          (fun _ => ℕ) (fun _ => Finset.range N) := by
      ext v
      simp only [Fintype.mem_piFinset]
    rw [hpi]
    simpa only [R, Int.cast_add] using hbad
  obtain ⟨χ, hχ, hnorm, _, _, hcoeff⟩ := hinv R r hr hR N hN F hF hB hbad'
  let P := roughVectorMvProjection χ.toLinearMap r
  have hP : P.totalDegree ≤ d := roughVectorMvProjection_degree _ hr
  have he : P = roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
      (roughScalarSpatialProjection χ.toLinearMap p z) := rough_vector_spatial_affine_projection _ z _ _ p
  refine ⟨χ, hnorm, hχ, (fun J => mvPolynomialBinomialCoefficient P d J),
    mvPolynomialBinomialCoefficient P d 0, ?_, ?_⟩
  · rw [← he]
    exact mv_polynomial_binomial_positive_expansion P d hP
  · intro J hJ
    have h := hcoeff J ((rough_spatial_degree_indices_mem d J).mp hJ).1
    have hpow : 0 < (N : ℝ)^(∑ j, J j) := pow_pos (by exact_mod_cast hN) _
    have hv : ‖((mvPolynomialBinomialCoefficient P d J : ℝ) : UnitAddCircle)‖ ≤
        (M : ℝ)/(N : ℝ)^(∑ j, J j) :=
      (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv, inv_pow] using hv

end Hindman168
