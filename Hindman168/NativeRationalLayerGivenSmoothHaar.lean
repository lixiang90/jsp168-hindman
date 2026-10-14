import Hindman168.NativeRationalLayerSmoothLocalHaar
import Hindman168.NativeCommonSmoothCurve

/-! The actual local law for a GIVEN common smooth-action limit witness. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_given_smooth_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (c : ℕ → D.G) (as : List (NativeSequentialBinomialFactor D))
    (h : ℝ → D.G) (hfreeze : NativeSmoothActionLimit D L c as h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
      ∀ beta ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
        ∀ rho : D.G, ∀ hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ,
        ∀ d : ℚ, d ≠ 0 → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
          ∀ᶠ n in atTop, ∀ b : ℝ, ∀ m : ℕ, τ*L n ≤ m →
            (∀ x ∈ scalarMvIntegerCube Unit m, |(b+(d : ℝ)*(x () : ℝ))/L n-beta| < r) →
            ∀ f ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
              ‖finiteComplexSetMean (scalarMvIntegerCube Unit m) (fun x =>
                f ((c n * nativeSequentialFactorsLeft D n (b+(d : ℝ)*(x () : ℝ)) as) •
                  (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                    (roughVectorMvEval (E := D.E) (p n) (fun i => b+(d : ℝ)*(x i : ℝ))) * rho : D.G ⧸ D.Γ))) -
                ∫ y, f y ∂nativeRationalLayerHaarImage D F 0 rho hRat (h beta)‖ < ε := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta ε hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨r,hr,hfr⟩ := hfreeze beta (ε/3) he
  refine ⟨r,hr,?_⟩
  intro rho hRat d hd τ hτ hτ1
  have heq := native_rational_layer_frozen_window_haar D F rho hRat L hL p hp hIrr
    d hd τ hτ hτ1 {h beta} isCompact_singleton (ε/3) he
    (unitLipschitzObservables (D.G ⧸ D.Γ)) (unit_lipschitz_observables_compact _)
  filter_upwards [hfr,heq,hL.eventually (eventually_gt_atTop 0)] with n hn hq hLn
  intro b m hm hloc f hf
  let orbit : (Unit → ℤ) → D.G ⧸ D.Γ := fun x =>
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p n) (fun i => b+(d : ℝ)*(x i : ℝ))) * rho : D.G ⧸ D.Γ)
  let moving : (Unit → ℤ) → ℂ := fun x =>
    f ((c n * nativeSequentialFactorsLeft D n (b+(d : ℝ)*(x () : ℝ)) as) • orbit x)
  let frozen : (Unit → ℤ) → ℂ := fun x => f (h beta • orbit x)
  have hdiff : ∀ x ∈ scalarMvIntegerCube Unit m, ‖moving x-frozen x‖ ≤ ε/3 := by
    intro x hx
    have hz := hn ((b+(d : ℝ)*(x () : ℝ))/L n) (hloc x hx) (orbit x)
    have hid : L n*((b+(d : ℝ)*(x () : ℝ))/L n) = b+(d : ℝ)*(x () : ℝ) :=
      mul_div_cancel₀ _ (ne_of_gt hLn)
    rw [hid] at hz
    have hdist := hf.1.dist_le_mul
      ((c n * nativeSequentialFactorsLeft D n (b+(d : ℝ)*(x () : ℝ)) as) • orbit x)
      (h beta • orbit x)
    have hnorm : ‖moving x-frozen x‖ ≤ dist
        ((c n * nativeSequentialFactorsLeft D n (b+(d : ℝ)*(x () : ℝ)) as) • orbit x)
        (h beta • orbit x) := by
      simpa only [moving, frozen, dist_eq_norm, NNReal.coe_one, one_mul] using hdist
    exact hnorm.trans hz.le
  have hb := finiteComplexSetMean_norm_bound (scalarMvIntegerCube Unit m)
    (fun x => moving x-frozen x) (ε/3) he.le hdiff
  have hid : finiteComplexSetMean (scalarMvIntegerCube Unit m) (fun x => moving x-frozen x) =
      finiteComplexSetMean (scalarMvIntegerCube Unit m) moving -
      finiteComplexSetMean (scalarMvIntegerCube Unit m) frozen := by
    simp only [finiteComplexSetMean, Finset.sum_sub_distrib, sub_div]
  rw [hid] at hb
  have hq' : ‖finiteComplexSetMean (scalarMvIntegerCube Unit m) frozen -
      ∫ y, f y ∂nativeRationalLayerHaarImage D F 0 rho hRat (h beta)‖ < ε/3 := by
    simpa only [frozen, orbit, MulAction.Quotient.smul_coe, smul_eq_mul, mul_assoc]
      using hq b m hm (h beta) (mem_singleton _) f hf
  change ‖finiteComplexSetMean (scalarMvIntegerCube Unit m) moving - _‖ < ε
  have ht := dist_triangle (finiteComplexSetMean (scalarMvIntegerCube Unit m) moving)
    (finiteComplexSetMean (scalarMvIntegerCube Unit m) frozen)
    (∫ y, f y ∂nativeRationalLayerHaarImage D F 0 rho hRat (h beta))
  simp only [dist_eq_norm] at ht
  linarith

end Hindman168
