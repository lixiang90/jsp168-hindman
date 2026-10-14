import Hindman168.NativeOriginalRealBadPairCharacters
import Hindman168.RoughOriginalBadPairScaleThresholds

/-! ONE fixed original finite character list and coefficient budget now
work eventually for ALL dyadic rough steps, raw sources, boxes and observables.
Actual PowerDominates supplies the thresholds; no production premise remains. -/
namespace Hindman168
open MeasureTheory MvPolynomial Filter
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_asymptotic_bad_pair_characters {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hg : PowerDominates atTop Z Scale)
    (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w) (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A : ℝ, 0 < A ∧ ∀ᶠ w in atTop,
      ∀ t : ℕ, Scale w ≤ t → (t : ℝ) < 2*Scale w →
      ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
        RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ z : ℕ, RoughNativeBadIndex D Q z t (Z w) c C L B η →
        ∃ χ ∈ S, ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
          (pOb=1 ∨ pOb=t) ∧ (∀ j, bOb j ≤ pOb) ∧
          ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
            ‖((coeff (Finsupp.equivFunOnFinite.symm J)
              (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                (roughScalarSpatialProjection χ p (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
                  A*((pOb : ℝ)/(Z w))^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,Z0,hA,hZ0,hProduce⟩ := native_original_real_bad_pair_characters D n d c C B η L hc hC hB hη
  refine ⟨S,hS,A,hA,?_⟩
  filter_upwards [rough_original_bad_pair_scale_thresholds hg hScale hZ c Z0 hc hZ0] with w hw
  intro t htlo hthi Q p hp hQ z hBad
  obtain ⟨ht,hZt,htZ,htc⟩ := hw.2 t htlo hthi
  exact hProduce t ht (Z w) hw.1 hZt htZ htc Q p hp hQ z hBad

end Hindman168
