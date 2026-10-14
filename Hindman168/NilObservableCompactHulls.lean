import Hindman168.NilCornerUniformRecipes

/-! Compact hulls in the fixed topology. A compatible supplied metric
keeps its original numerical distances and Lipschitz constants. -/

namespace Hindman168
open NNReal BoundedContinuousFunction
open scoped Classical

theorem compatibleMetric_boundedLipschitz_compact_hull {X : Type*}
    [t : TopologicalSpace X] [CompactSpace X] (M : MetricSpace X)
    (ht : t = M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (A : Set C(X, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B)
    (hL : ∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ (L : ℝ) * @dist X M.toDist x y) :
    ∃ H : Set C(X, ℝ), IsCompact H ∧ A ⊆ H := by
  letI : MetricSpace X := M.replaceTopology ht
  have hl : ∀ f ∈ A, LipschitzWith L f := by
    intro f hf
    exact LipschitzWith.of_dist_le_mul (hL f hf)
  exact boundedLipschitz_observable_compact_hull A B L hB hl

theorem boundedEquicontinuous_observable_compact_hull {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (A : Set C(X, ℝ)) (B : ℝ) (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B)
    (hE : Equicontinuous (fun f : A => fun x => f.val x)) :
    ∃ H : Set C(X, ℝ), IsCompact H ∧ A ⊆ H := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  let D : Set (X →ᵇ ℝ) := e '' A
  have hpre (f : D) : e.symm f.val ∈ A := by
    obtain ⟨g, hg, heq⟩ := f.property
    rw [← heq, e.symm_apply_apply]
    exact hg
  have heq : (fun f : D => fun x => f.val x) =
      (fun f : D => fun x => (e.symm f.val) x) := by
    funext f x
    rfl
  have hEc : Equicontinuous (fun f : D => fun x => f.val x) := by
    rw [heq]
    exact hE.comp (fun f => ⟨e.symm f.val, hpre f⟩)
  have hc : IsCompact (closure D) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc D
    · intro f x hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact abs_le.mp (hB g hg x)
    · exact hEc
  refine ⟨e.symm '' closure D, hc.image e.symm.continuous, ?_⟩
  intro f hf
  exact ⟨e f, subset_closure ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩

end Hindman168
