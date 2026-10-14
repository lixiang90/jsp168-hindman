import Hindman168.FiniteComplexDiscrepancyAnchor
import Hindman168.NativeRationalWeightedInverseStatement

/-! Actual nonuniform source samples construct a TRUE weighted constant
native polynomial with at least the original discrepancy at EVERY positive
length. This allows the proved large-N induction step to handle small N
without an assumed original horizontal-character existence theorem. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalConstantPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (v : D.E) : RoughVectorMvPolynomial Unit D.E :=
  [(MvPolynomial.C 1,v)]

theorem native_rational_constant_polynomial_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (v : D.E) (x : Unit → ℝ) :
    roughVectorMvEval (nativeRationalConstantPolynomial D v) x=v := by
  simp [nativeRationalConstantPolynomial,roughVectorMvEval]

theorem native_rational_constant_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (v : D.E) :
    RoughVectorMvWeightedDegree L.layer (nativeRationalConstantPolynomial D v) 0 := by
  intro term ht
  have he : term=(MvPolynomial.C 1,v) := List.mem_singleton.mp ht
  subst term
  change v ∈ L.layer ((MvPolynomial.C (1 : ℝ)).totalDegree+0)
  rw [MvPolynomial.totalDegree_C,zero_add,L.zero]
  trivial

theorem native_rational_constant_discrepancy_anchor {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
    δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit N) (nativeMvPolynomialOrbit D p) H‖ →
    ∃ v : D.E, ∀ M : ℕ, 0 < M →
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit M)
        (nativeMvPolynomialOrbit D (nativeRationalConstantPolynomial D v)) H‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H hBad
  obtain ⟨x,_hx,hPoint⟩ := finite_complex_discrepancy_anchor (scalarMvIntegerCube Unit N)
    (scalar_mv_integer_cube_nonempty Unit N hN) (fun x => H (nativeMvPolynomialOrbit D p x))
    (∫ q, H q ∂nativeNilmanifoldQuotientProbability D)
  let v := roughVectorMvEval (E := D.E) p (fun i => (x i : ℝ))
  refine ⟨v,?_⟩
  intro M hM
  have hSame (y : Unit → ℤ) :
      nativeMvPolynomialOrbit D (nativeRationalConstantPolynomial D v) y=nativeMvPolynomialOrbit D p x := by
    rw [nativeMvPolynomialOrbit,nativeMvPolynomialOrbit,native_rational_constant_polynomial_eval]
  change δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube Unit M)
    (fun y => H (nativeMvPolynomialOrbit D (nativeRationalConstantPolynomial D v) y))-_‖
  simp_rw [hSame]
  rw [finite_complex_set_mean_const_nonempty _ (scalar_mv_integer_cube_nonempty Unit M hM)]
  exact hBad.trans hPoint

end Hindman168
