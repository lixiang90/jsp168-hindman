import Hindman168.NativeRationalWeightedPolynomialRecursion
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! On the ACTUAL terminal group, canonical native Haar discrepancy vanishes
for every nonempty finite sample. Empty samples are deliberately excluded. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_subsingleton_finite_discrepancy {s : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) [Subsingleton D.G] (a : Finset α) (ha : a.Nonempty)
    (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ), nativeNilmanifoldFiniteDiscrepancy D a f H = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_nilmanifold_quotient_probability_isProbability D
  letI : Subsingleton (D.G ⧸ D.Γ) := (QuotientGroup.mk_surjective (s := D.Γ)).subsingleton
  intro H
  have hc : (a.card : ℂ) ≠ 0 := by exact_mod_cast ha.card_pos.ne'
  have hValue : ∀ q : D.G ⧸ D.Γ, H q = H (1 : D.G) :=
    fun q => congrArg H (Subsingleton.elim q (1 : D.G))
  have hMean : finiteComplexSetMean a (fun x => H (f x)) = H (1 : D.G) := by
    simp only [finiteComplexSetMean,hValue,Finset.sum_const,nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ hc
  have hIntegral : (∫ q, H q ∂nativeNilmanifoldQuotientProbability D) = H (1 : D.G) := by
    have he : (fun q : D.G ⧸ D.Γ => H q) = (fun _ : D.G ⧸ D.Γ => H (1 : D.G)) := funext hValue
    rw [he]
    simp
  change finiteComplexSetMean a (fun x => H (f x)) -
    (∫ q, H q ∂nativeNilmanifoldQuotientProbability D) = 0
  rw [hMean,hIntegral,sub_self]

theorem native_rational_weighted_terminal_canonical_discrepancy {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (a : Finset (Unit → ℤ)) (ha : a.Nonempty) :
    let T := (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2
    letI : MeasurableSpace T.1.E := borel T.1.E
    letI : MeasurableSpace T.1.G := borel T.1.G
    letI := T.1.metric
    letI : TopologicalSpace (T.1.G ⧸ T.1.Γ) := T.1.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(T.1.G ⧸ T.1.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy T.1 a (nativeMvPolynomialOrbit T.1 T.2.2.val) H = 0 := by
  let T := (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2
  letI : MeasurableSpace T.1.E := borel T.1.E
  letI : MeasurableSpace T.1.G := borel T.1.G
  letI := T.1.metric
  letI : TopologicalSpace (T.1.G ⧸ T.1.Γ) := T.1.metric.toUniformSpace.toTopologicalSpace
  letI := native_rational_weighted_polynomial_recursion_terminal_group D F p hp shifts
  exact native_rational_subsingleton_finite_discrepancy T.1 a ha (nativeMvPolynomialOrbit T.1 T.2.2.val)

end Hindman168
