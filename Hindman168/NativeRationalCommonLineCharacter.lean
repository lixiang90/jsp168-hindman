import Hindman168.NativeRationalLineCharacterProduction
import Hindman168.LeibmanCubeCommonSpanningDirections

/-! ACTUAL native cube discrepancy now yields ONE SAME original finite
horizontal character on dense short-line directions and dense basepoints.
Line production comes from the PROVED Unit inverse; no analytic production
oracle is assumed. Original Haar/metric and both line tables are retained. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators Classical
universe u

def NativeRationalLineBounds {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E) (ℓ Q H : ℕ)
    (χ : D.E →L[ℝ] ℝ) (q : κ → ℕ) (x : κ → ℤ) : Prop :=
  (∀ r : ℕ, 0 < r →
    (H : ℝ)^r*‖((MvPolynomial.eval (fun j => (x j : ℝ))
      (scalarMvLineCoefficient (roughVectorMvProjection χ.toLinearMap p)
        (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
  ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
    (H : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
      (roughVectorMvProjection χ.toLinearMap (nativeRationalLinePolynomial D p x q)) ℓ I : ℝ) :
        UnitAddCircle)‖ ≤ (Q : ℝ)

theorem native_rational_common_line_character {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ Q : ℕ, 0 < Q ∧ ∀ (N K d : ℕ), 0 < K → K^2 ≤ N →
      8*(n : ℝ) ≤ (δ/2)*(K : ℝ) →
      8*(d : ℝ)*((nativeRationalLineCharacterPool D Q).card : ℝ) < (δ/2)*(K : ℝ) →
      ∀ p : RoughVectorMvPolynomial (Fin n) D.E, RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
          (nativeMvPolynomialOrbit D p) F‖ →
        ∃ χ ∈ nativeRationalLineCharacterPool D Q, ∃ T : Finset (Fin n → ℕ),
          T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range K) ∧ d*K^n < T.card*K ∧
          ∀ q ∈ T, (δ/2)/(8*((nativeRationalLineCharacterPool D Q).card : ℝ))*
            ((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
            (((scalarMvIntegerCube (Fin n) N).filter
              (NativeRationalLineBounds D p ℓ Q (N/K^2) χ q)).card : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Q,hQ,hProduce⟩ := native_rational_line_character_production (κ := Fin n) D L (δ/2) (by positivity)
  refine ⟨Q,hQ,?_⟩
  intro N K d hK hKN hSize hDir p hp F hF hBad
  let f (x : Fin n → ℤ) := F (nativeMvPolynomialOrbit D p x)-
    ∫ z, F z ∂nativeNilmanifoldQuotientProbability D
  have hN : 0 < N := lt_of_lt_of_le (by positivity : 0 < K^2) hKN
  have hCube : scalarMvIntegerCube (Fin n) N =
      Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ)) := by
    ext x
    simp only [scalarMvIntegerCube,Fintype.mem_piFinset]
  have hH : 0 < N/K^2 := Nat.div_pos hKN (by positivity)
  have hInt := native_nilmanifold_probability_integral_bound D F 1 hF.2
  have hf (x : Fin n → ℤ) : ‖f x‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by simpa only [one_add_one_eq_two] using add_le_add (hF.2 _) hInt)
  have hMean : (δ/2)*2 ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N) f‖ := by
    rw [show (δ/2)*2=δ by ring]
    dsimp only [f]
    rw [finiteComplexSetMean_sub_const _ (scalar_mv_integer_cube_nonempty (Fin n) N hN)]
    exact hBad
  have hProduction : ∀ q ∈ Fintype.piFinset (fun _ : Fin n => Finset.range K),
      ∀ x ∈ Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ)),
      (δ/2)*2/2 ≤ ‖finiteComplexSetMean (Finset.range (N/K^2))
        (fun m => f (fun j => x j+(q j : ℤ)*(m : ℤ)))‖ →
      ∃ χ ∈ nativeRationalLineCharacterPool D Q, NativeRationalLineBounds D p ℓ Q (N/K^2) χ q x := by
    intro q _hq x _hx hLine
    have hLine' : δ/2 ≤ ‖finiteComplexSetMean (Finset.range (N/K^2))
        (fun m => f (fun j => x j+(q j : ℤ)*(m : ℤ)))‖ := by
      simpa only [mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hLine
    exact hProduce p hp x q (N/K^2) hH F hF hLine'
  have hSelected := leibman_equal_cube_common_dense_directions N K d hK hKN f 2 (δ/2) (by norm_num) (by positivity)
    hSize hf (by simpa only [hCube] using hMean) (nativeRationalLineCharacterPool D Q)
    (NativeRationalLineBounds D p ℓ Q (N/K^2)) hDir hProduction
  simpa only [← hCube] using hSelected

end Hindman168
