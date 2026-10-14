import Hindman168.NativeRationalConstantDiscrepancyAnchor

/-! Every true finite-variable native discrepancy has an ACTUAL constant
source anchor preserving that discrepancy at ALL positive equal-cube lengths.
No nontriviality or horizontal-character existence premise is inserted. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalConstantMvPolynomial {s : ℕ} (κ : Type*)
    (D : NativeNilmanifoldData.{u} s) (v : D.E) : RoughVectorMvPolynomial κ D.E :=
  [(MvPolynomial.C 1,v)]

theorem native_rational_constant_mv_polynomial_eval {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (v : D.E) (x : κ → ℝ) :
    roughVectorMvEval (nativeRationalConstantMvPolynomial κ D v) x=v := by
  simp [nativeRationalConstantMvPolynomial,roughVectorMvEval]

theorem native_rational_constant_mv_polynomial_weighted {s ℓ : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (v : D.E) :
    RoughVectorMvWeightedDegree L.layer (nativeRationalConstantMvPolynomial κ D v) 0 := by
  intro term ht
  have he : term=(MvPolynomial.C 1,v) := List.mem_singleton.mp ht
  subst term
  change v ∈ L.layer ((MvPolynomial.C (1 : ℝ)).totalDegree+0)
  rw [MvPolynomial.totalDegree_C,zero_add,L.zero]
  trivial

theorem native_rational_constant_mv_discrepancy_anchor {s : ℕ} {κ : Type*} [Fintype κ]
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
    δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube κ N) (nativeMvPolynomialOrbit D p) F‖ →
    ∃ v : D.E, ∀ T : ℕ, 0 < T →
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube κ T)
        (nativeMvPolynomialOrbit D (nativeRationalConstantMvPolynomial κ D v)) F‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F hBad
  obtain ⟨x,_hx,hPoint⟩ := finite_complex_discrepancy_anchor (scalarMvIntegerCube κ N)
    (scalar_mv_integer_cube_nonempty κ N hN) (fun x => F (nativeMvPolynomialOrbit D p x))
    (∫ z, F z ∂nativeNilmanifoldQuotientProbability D)
  let v := roughVectorMvEval (E := D.E) p (fun j => (x j : ℝ))
  refine ⟨v,?_⟩
  intro T hT
  have hSame (y : κ → ℤ) : nativeMvPolynomialOrbit D (nativeRationalConstantMvPolynomial κ D v) y =
      nativeMvPolynomialOrbit D p x := by
    rw [nativeMvPolynomialOrbit,nativeMvPolynomialOrbit,native_rational_constant_mv_polynomial_eval]
  change δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube κ T)
    (fun y => F (nativeMvPolynomialOrbit D (nativeRationalConstantMvPolynomial κ D v) y))-_‖
  simp_rw [hSame]
  rw [finite_complex_set_mean_const_nonempty _ (scalar_mv_integer_cube_nonempty κ T hT)]
  exact hBad.trans hPoint

end Hindman168
