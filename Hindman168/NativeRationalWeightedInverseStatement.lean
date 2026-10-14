import Hindman168.NativeRationalDegreeOneFiniteVariablesInverse
import Hindman168.NativeRationalTerminalPolynomialDiscrepancy

/-! The FULL desired rational-filtration inverse conclusion is a named
proposition, NOT an axiom or data field. Only the genuine degree-zero/one
base cases are proved here; higher-degree induction remains open. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u

def NativeRationalWeightedInverseStatement {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (σ : Type*) [Fintype σ] : Prop :=
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial σ D.E,
    RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
      ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
        ∃ χ : D.E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
          (∀ J : σ → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
          ∀ J : σ → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)

theorem native_rational_weighted_inverse_degree_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 1) (σ : Type*) [Fintype σ] :
    NativeRationalWeightedInverseStatement D L σ :=
  native_rational_degree_one_finite_variables_inverse D L σ

theorem native_rational_weighted_inverse_degree_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 0) (σ : Type*) [Fintype σ] :
    NativeRationalWeightedInverseStatement D L σ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_rational_degree_zero_group_subsingleton D L
  intro δ hδ
  refine ⟨1,Nat.zero_lt_one,?_⟩
  intro p _ N hN H _ hLarge
  have he := native_rational_subsingleton_finite_discrepancy D (scalarMvIntegerCube σ N)
    (scalar_mv_integer_cube_nonempty σ N hN) (nativeMvPolynomialOrbit D p) H
  rw [he,norm_zero] at hLarge
  exact False.elim (not_le_of_gt hδ hLarge)

end Hindman168
