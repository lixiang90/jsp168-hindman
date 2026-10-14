import Hindman168.NativeResidueCubeSmoothLocalHaar
import Hindman168.NativeCommonSmoothCurve

/-! The actual local law for a GIVEN common smooth-action limit witness. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_given_smooth_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (cN : ℕ → D.G) (as : List (NativeSequentialBinomialFactor D))
    (h : ℝ → D.G) (hfreeze : NativeSmoothActionLimit D L cN as h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
      ∀ beta ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
        ∀ d n : ℕ, ∀ e : Fin (n+1) ≃ Finset (Fin d),
        ∀ ρ : D.G, ∀ hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ,
        ∀ t : ℕ, 0 < t → ∀ c R : ℝ, 0 < c → 0 ≤ R →
          ∀ᶠ m in atTop, ∀ lo hi v : Fin (d+1) → ℤ,
            (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
            (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
            (∀ x ∈ alignmentBoxClass lo hi v t, ∀ V : Finset (Fin d),
              |((x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))/L m-beta| < r) →
            ∀ f ∈ unitLipschitzObservables (Finset (Fin d) → D.G ⧸ D.Γ),
              ‖finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (fun V =>
                (cN m * nativeSequentialFactorsLeft D m ((x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ)) as) •
                (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                  (roughVectorMvEval (E := D.E) (p m) (fun _ => (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))) * ρ : D.G ⧸ D.Γ))) -
                ∫ y, f y ∂nativeResidueCubeHaarImage D F ρ hρ d n e (h beta)‖ < ε := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro beta ε hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨r,hr,hfr⟩ := hfreeze beta (ε/3) he
  refine ⟨r,hr,?_⟩
  intro d n e ρ hρ t ht c R hc hR
  have hq := native_residue_cube_frozen_progression_haar D F ρ hρ d n e L hL p hp hIrr
    t ht c R (ε/3) hc hR he {h beta} isCompact_singleton
    (unitLipschitzObservables (Finset (Fin d) → D.G ⧸ D.Γ)) (unit_lipschitz_observables_compact _)
  filter_upwards [hfr,hq,hL.eventually (eventually_gt_atTop 0)] with m hm hq' hLm
  intro lo hi v hlen hloc hlocal f hf
  let time : (Fin (d+1) → ℤ) → Finset (Fin d) → ℝ := fun x V =>
    (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ)
  let orbit : (Fin (d+1) → ℤ) → Finset (Fin d) → D.G ⧸ D.Γ := fun x V =>
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p m) (fun _ => time x V)) * ρ : D.G ⧸ D.Γ)
  let moving := fun x V => (cN m * nativeSequentialFactorsLeft D m (time x V) as) • orbit x V
  let frozen := fun x V => h beta • orbit x V
  have hclose : ∀ x ∈ alignmentBoxClass lo hi v t, ‖f (moving x)-f (frozen x)‖ ≤ ε/3 := by
    intro x hx
    have hd : dist (moving x) (frozen x) ≤ ε/3 := by
      apply (dist_pi_le_iff he.le).mpr
      intro V
      have hv := hm (time x V/L m) (hlocal x hx V) (orbit x V)
      rw [mul_div_cancel₀ _ (ne_of_gt hLm)] at hv
      exact hv.le
    have hf' := hf.1.dist_le_mul (moving x) (frozen x)
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hf'
    exact hf'.trans hd
  have hmean := finite_complex_set_mean_observable_difference (alignmentBoxClass lo hi v t)
    (fun x => f (moving x)) (fun x => f (frozen x)) (ε/3) he.le hclose
  have hhaar : ‖finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (frozen x)) -
      ∫ y, f y ∂nativeResidueCubeHaarImage D F ρ hρ d n e (h beta)‖ < ε/3 := by
    simpa only [frozen, orbit, time, MulAction.Quotient.smul_coe, smul_eq_mul, mul_assoc]
      using hq' lo hi v hlen hloc (h beta) (mem_singleton _) f hf
  change ‖finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (moving x)) - _‖ < ε
  have htri := dist_triangle (finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (moving x)))
    (finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (frozen x)))
    (∫ y, f y ∂nativeResidueCubeHaarImage D F ρ hρ d n e (h beta))
  simp only [dist_eq_norm] at htri
  linarith

end Hindman168
