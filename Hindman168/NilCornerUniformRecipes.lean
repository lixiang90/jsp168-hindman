import Hindman168.NilCornerBoundedRecipe
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz

/-! A compact observable family admits finitely many normalized recipes
at each accuracy, with one finite total-coefficient bound. Bounded
Lipschitz families have a compact hull by Arzela--Ascoli. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal BoundedContinuousFunction

variable {ι X K : Type*} [Fintype ι] [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace K] [CompactSpace K]

theorem cornerRecipe_compact_family [T35Space X]
    (vertex : ι → C(K, X)) (hinj : Function.Injective (fun x => fun j => vertex j x))
    (root : C(K, X)) (A : Set C(X, ℝ)) (hA : IsCompact A) (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe ι X), ∃ B : ℝ, 0 ≤ B ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ B) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ x, |r.eval vertex x - f (root x)| < ε) := by
  obtain ⟨t, _, htfin, htcover⟩ := hA.finite_cover_balls (half_pos hε)
  letI : Fintype t := htfin.fintype
  have hrecipe : ∀ f : t, ∃ r : CornerProductRecipe ι X, r.Bounded ∧
      ∀ x, |r.eval vertex x - f.val (root x)| < ε / 2 := by
    intro f
    exact cornerRecipe_bounded_uniform_approximation vertex hinj (f.val.comp root)
      (ε / 2) (half_pos hε)
  choose recipe hbounded happrox using hrecipe
  let recipes : Finset (CornerProductRecipe ι X) := Finset.univ.image recipe
  let B : ℝ := ∑ f : t, (recipe f).coefficientMass
  refine ⟨recipes, B, Finset.sum_nonneg (fun _ _ => cornerRecipe_coefficientMass_nonneg _), ?_, ?_⟩
  · intro r hr
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨hbounded f, Finset.single_le_sum (fun _ _ => cornerRecipe_coefficientMass_nonneg _)
      (Finset.mem_univ f)⟩
  · intro f hf
    obtain ⟨g, hgt, hfg⟩ := Set.mem_iUnion₂.mp (htcover hf)
    let g' : t := ⟨g, hgt⟩
    refine ⟨recipe g', Finset.mem_image.mpr ⟨g', Finset.mem_univ _, rfl⟩, ?_⟩
    intro x
    have hdist : dist f g < ε / 2 := hfg
    have hpoint : |g (root x) - f (root x)| < ε / 2 := by
      have hp := ContinuousMap.dist_apply_le_dist (f := g) (g := f) (root x)
      have hdg : dist g f < ε / 2 := by simpa only [dist_comm] using hdist
      simpa only [Real.dist_eq] using hp.trans_lt hdg
    calc
      |(recipe g').eval vertex x - f (root x)| ≤
          |(recipe g').eval vertex x - g (root x)| + |g (root x) - f (root x)| :=
        abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (happrox g' x) hpoint
      _ = ε := add_halves ε

omit [Fintype ι] [TopologicalSpace K] [CompactSpace K] in
theorem boundedLipschitz_observable_compact_hull {X : Type*} [MetricSpace X] [CompactSpace X]
    (A : Set C(X, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B)
    (hL : ∀ f ∈ A, LipschitzWith L f) :
    ∃ H : Set C(X, ℝ), IsCompact H ∧ A ⊆ H := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  let D : Set (X →ᵇ ℝ) := e '' A
  have hDc : IsCompact (closure D) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc D
    · intro f x hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact abs_le.mp (hB g hg x)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L : ℝ) * r)
        (by
          have hc : Continuous (fun r : ℝ => (L : ℝ) * r) := continuous_const.mul continuous_id
          simpa only [mul_zero] using hc.tendsto (0 : ℝ))
      intro x y f
      obtain ⟨g, hg, heq⟩ := f.property
      have hp := (hL g hg).dist_le_mul x y
      rw [← heq]
      exact hp
  refine ⟨e.symm '' closure D, hDc.image e.symm.continuous, ?_⟩
  intro f hf
  exact ⟨e f, subset_closure ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩

theorem cornerRecipe_boundedLipschitz_family {X : Type*} [MetricSpace X] [CompactSpace X]
    (vertex : ι → C(K, X)) (hinj : Function.Injective (fun x => fun j => vertex j x))
    (root : C(K, X)) (A : Set C(X, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe ι X), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ x, |r.eval vertex x - f (root x)| < ε) := by
  obtain ⟨H, hH, hAH⟩ := boundedLipschitz_observable_compact_hull A B L hB hL
  obtain ⟨recipes, C, hC, hb, ha⟩ := cornerRecipe_compact_family vertex hinj root H hH ε hε
  exact ⟨recipes, C, hC, hb, fun f hf => ha f (hAH hf)⟩

end Hindman168
