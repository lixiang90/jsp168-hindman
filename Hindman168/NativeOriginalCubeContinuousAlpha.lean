import Hindman168.NativeOriginalCubeBoundedAlpha
import Hindman168.FiniteProbabilityDiscrepancy

/-! Actual original alpha-box limits for every continuous test. This permits
continuous projected pullbacks without assuming Lipschitz projections/actions. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_cube_continuous_alpha_test {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G)
    (hlaw : NativeCubeBoundedAlphaHaarLaw D H L P M hM sigma hRat h) (q : Fin (s+2)) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ f : C((Finset (Fin q.val) → D.G ⧸ D.Γ), ℂ),
  ∀ beta c C : ℝ, 0 < c → 0 ≤ C → ∀ ε : ℝ, 0 < ε →
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 < α → α < α0 →
      ∀ t : ℕ, 0 < t → (M : ℤ) ∣ (t : ℤ) →
      ∀ᶠ m in atTop, ∀ lo hi : Fin (q.val+1) → ℝ, ∀ v : Fin (q.val+1) → ℤ,
        (∀ i : Fin q.val, (M : ℤ) ∣ v i.succ) →
        (∀ j, c*α*L m ≤ hi j-lo j ∧ hi j-lo j ≤ C*α*L m) →
        (|lo 0-beta*L m| ≤ C*α*L m ∧ |hi 0-beta*L m| ≤ C*α*L m) →
        (∀ i : Fin q.val, |lo i.succ| ≤ C*α*L m ∧ |hi i.succ| ≤ C*α*L m) →
          ‖finiteComplexSetMean (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t)
            (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) -
            ∫ y, f y ∂nativeResidueCubeHaarImage D H
              (sigma (signedPeriodResidue M hM (v 0))) (hRat _)
              q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)‖ < ε
 := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  intro f beta c C hc hC ε hε
  obtain ⟨g,⟨T,hT⟩,hclose⟩ := compact_lipschitz_uniform_approximation _ f (ε/6) (by positivity)
  obtain ⟨α0,hα0,ha⟩ := hlaw beta c C hc hC ‖g‖ (norm_nonneg g) T (ε/3) (by positivity)
  refine ⟨α0,hα0,?_⟩
  intro α hα hα' t ht hMt
  filter_upwards [ha α hα hα' t ht hMt] with m hm
  intro lo hi v hv hlen hbase hinc
  have hg := hm q lo hi v hv hlen hbase hinc g hT g.norm_coe_le_norm
  let μ := nativeResidueCubeHaarImage D H (sigma (signedPeriodResidue M hM (v 0))) (hRat _)
    q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)
  letI : IsProbabilityMeasure μ := native_residue_cube_haar_isProbability D H _ _ _ _ _ _
  let S := alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t
  let orbit := fun x : Fin (q.val+1) → ℤ => fun V : Finset (Fin q.val) =>
    (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ)
  let Λ := finiteProbabilityDiscrepancy μ S orbit
  have herr := linear_discrepancy_approximation_error _ Λ (finite_probability_discrepancy_norm μ S orbit)
    f g (ε/6) hclose
  have htri : ‖Λ f‖ ≤ ‖Λ f-Λ g‖+‖Λ g‖ := by
    simpa only [sub_add_cancel] using norm_add_le (Λ f-Λ g) (Λ g)
  change ‖Λ g‖ < ε/3 at hg
  change ‖Λ f‖ < ε
  linarith

end Hindman168
