import Hindman168.FinitePolynomialHullBound
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Uniform positive-part correlations on the closed convex hull

The polynomial approximation error is charged to the actual weighted mass.
For each desired error a fixed polynomial is chosen before the stage tends
to infinity. No degree varying with the stage is assumed pseudorandom.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped BigOperators Topology Classical

theorem closedConvexHull_abs_le {α : Type*} (S : Set (α → ℝ)) (K : ℝ)
    (hS : ∀ f ∈ S, ∀ x, |f x| ≤ K) {G : α → ℝ}
    (hG : G ∈ closedConvexHull ℝ S) : ∀ x, |G x| ≤ K := by
  let box : Set (α → ℝ) := {f | ∀ x, |f x| ≤ K}
  have hconv : Convex ℝ box := by
    intro f hf g hg a b ha hb hab x
    change |a * f x + b * g x| ≤ K
    calc
      _ ≤ |a * f x| + |b * g x| := abs_add_le _ _
      _ = a * |f x| + b * |g x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * K + b * K := add_le_add
        (mul_le_mul_of_nonneg_left (hf x) ha) (mul_le_mul_of_nonneg_left (hg x) hb)
      _ = K := by rw [← add_mul, hab, one_mul]
  have hclosed : IsClosed box := by
    have hi : IsClosed (⋂ x : α, {f : α → ℝ | |f x| ≤ K}) :=
      isClosed_iInter (fun x => isClosed_le (continuous_apply x).abs continuous_const)
    simpa only [box, Set.setOf_forall] using hi
  exact closedConvexHull_min hS hconv hclosed hG

theorem exists_positive_part_polynomial (K δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Polynomial ℝ, ∀ t, |t| ≤ K → |P.eval t - max t 0| < δ := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-K) K
    (fun t : ℝ => max t 0) (continuous_id.max continuous_const).continuousOn δ hδ
  exact ⟨P, fun t ht => hP t (abs_le.mp ht)⟩

theorem positive_part_polynomial_error {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (c H G : α → ℝ) (P : Polynomial ℝ) (K δ : ℝ)
    (hc : ∀ x, |c x| ≤ H x) (hG : ∀ x, |G x| ≤ K)
    (hP : ∀ t, |t| ≤ K → |P.eval t - max t 0| ≤ δ) :
    |expectation μ (fun x => c x * max (G x) 0) -
      expectation μ (fun x => c x * P.eval (G x))| ≤ δ * expectation μ H := by
  have he := weighted_centered_difference_bound μ hμ c H
    (fun x => max (G x) 0) (fun x => P.eval (G x)) hc
  have hH (x : α) : 0 ≤ H x := (abs_nonneg _).trans (hc x)
  have hbound : expectation μ (fun x => H x * |max (G x) 0 - P.eval (G x)|) ≤
      δ * expectation μ H := by
    calc
      _ ≤ expectation μ (fun x => δ * H x) := expectation_mono _ _ _ hμ (fun x => by
        rw [mul_comm δ]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hP _ (hG x)) (hH x))
      _ = _ := expectation_const_mul _ _ _
  exact he.trans hbound

theorem uniform_positive_part_closedConvexHull {α : Type*}
    (μ : ℕ → Mass α) (c H : ℕ → α → ℝ) (S : ℕ → Set (α → ℝ)) (K B : ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hc : ∀ᶠ w in atTop, ∀ x, |c w x| ≤ H w x)
    (hB : 0 ≤ B) (hmass : ∀ᶠ w in atTop, expectation (μ w) (H w) ≤ B)
    (hS : ∀ᶠ w in atTop, ∀ f ∈ S w, ∀ x, |f x| ≤ K)
    (hpoly : ∀ P : Polynomial ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ G ∈ closedConvexHull ℝ (S w),
        |expectation (μ w) (fun x => c w x * P.eval (G x))| < η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ G ∈ closedConvexHull ℝ (S w),
      |expectation (μ w) (fun x => c w x * max (G x) 0)| < η := by
  intro η hη
  let δ := η / (2 * (1 + B))
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨P, hP⟩ := exists_positive_part_polynomial K δ hδ
  have hcost : δ * B < η / 2 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity : 0 < 2 * (1 + B)) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  filter_upwards [hμ, hc, hmass, hS, hpoly P (η / 2) (by positivity)] with w hw hcw hmw hSw hpw
  intro G hG
  have hg := closedConvexHull_abs_le (S w) K hSw hG
  have he := positive_part_polynomial_error (μ w) hw (c w) (H w) G P K δ hcw hg
    (fun t ht => (hP t ht).le)
  have he' : |expectation (μ w) (fun x => c w x * max (G x) 0) -
      expectation (μ w) (fun x => c w x * P.eval (G x))| < η / 2 :=
    (he.trans (mul_le_mul_of_nonneg_left hmw hδ.le)).trans_lt hcost
  have htri := abs_add_le
    (expectation (μ w) (fun x => c w x * max (G x) 0) -
      expectation (μ w) (fun x => c w x * P.eval (G x)))
    (expectation (μ w) (fun x => c w x * P.eval (G x)))
  simp only [sub_add_cancel] at htri
  exact htri.trans_lt (by linarith [hpw G hG])

end Hindman168.FiniteMass
