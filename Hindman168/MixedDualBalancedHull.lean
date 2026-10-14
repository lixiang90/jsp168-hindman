import Hindman168.MixedDualConvexHull

namespace Hindman168
open scoped BigOperators Classical

theorem subgroupMixedDualFunction_neg_vertex {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d)) (hS : S ≠ ∅)
    (f : Finset (Fin d) → G → ℝ) (x : G) :
    subgroupMixedDualFunction Q d (fun ω y => (if ω = S then -1 else 1) * f ω y) x =
      -subgroupMixedDualFunction Q d f x := by
  unfold subgroupMixedDualFunction
  simp only [Finset.prod_mul_distrib]
  have hm : S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅ := by simp [hS]
  simp only [Finset.prod_ite_eq', if_pos hm, neg_one_mul]
  simp only [finiteHaarMean, Finset.sum_neg_distrib, neg_div]

theorem subgroupMixedDualHull_neg_mem {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (hd : 0 < d) {u : G → ℝ}
    (hu : u ∈ subgroupMixedDualHull Q d) : -u ∈ subgroupMixedDualHull Q d := by
  have hc : Convex ℝ (subgroupMixedDualHull Q d) := convex_convexHull ℝ _
  apply convexHull_min (t := {v : G → ℝ | -v ∈ subgroupMixedDualHull Q d}) ?_ ?_ hu
  · rintro v ⟨f, hf, rfl⟩
    let S : Finset (Fin d) := {⟨0, hd⟩}
    have hS : S ≠ ∅ := Finset.singleton_ne_empty _
    have h := subgroupMixedDualFunction_mem_hull Q d
      (fun ω y => (if ω = S then -1 else 1) * f ω y) (by
        intro ω hω y
        by_cases he : ω = S <;>
          simpa only [he, ↓reduceIte, neg_one_mul, one_mul, abs_neg] using hf ω hω y)
    change -subgroupMixedDualFunction Q d f ∈ subgroupMixedDualHull Q d
    convert h using 1
    funext x
    exact (subgroupMixedDualFunction_neg_vertex Q d S hS f x).symm
  · intro a ha b hb r s hr hs hrs
    change -(r • a + s • b) ∈ subgroupMixedDualHull Q d
    simpa only [neg_add_rev, neg_smul, smul_neg, add_comm] using hc ha hb hr hs hrs

theorem subgroupMixedDualHull_zero_mem {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (hd : 0 < d) :
    (0 : G → ℝ) ∈ subgroupMixedDualHull Q d := by
  have hc : Convex ℝ (subgroupMixedDualHull Q d) := convex_convexHull ℝ _
  have h := hc (subgroupMixedDualHull_one_mem Q d)
    (subgroupMixedDualHull_neg_mem Q d hd (subgroupMixedDualHull_one_mem Q d))
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [smul_neg, add_neg_cancel] using h

theorem convex_symmetric_span_representation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (hc : Convex ℝ S) (hz : (0 : E) ∈ S)
    (hn : ∀ x ∈ S, -x ∈ S) {z : E} (hzs : z ∈ Submodule.span ℝ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ u ∈ S, z = B • u := by
  induction hzs using Submodule.span_induction with
  | mem z hz => exact ⟨1, zero_le_one, z, hz, (one_smul ℝ z).symm⟩
  | zero => exact ⟨0, le_rfl, 0, hz, (zero_smul ℝ (0 : E)).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨B, hB, u, hu, rfl⟩ := hx
    obtain ⟨C, hC, v, hv, rfl⟩ := hy
    by_cases he : B + C = 0
    · have hb : B = 0 := by linarith
      have hc0 : C = 0 := by linarith
      exact ⟨0, le_rfl, 0, hz, by simp [hb, hc0]⟩
    · refine ⟨B + C, add_nonneg hB hC, (B / (B + C)) • u + (C / (B + C)) • v,
        hc hu hv (div_nonneg hB (add_nonneg hB hC)) (div_nonneg hC (add_nonneg hB hC))
          (by rw [← add_div, div_self he]), ?_⟩
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ he, mul_div_cancel₀ _ he]
  | smul r x _ hx =>
    obtain ⟨B, hB, u, hu, rfl⟩ := hx
    by_cases hr : 0 ≤ r
    · exact ⟨r * B, mul_nonneg hr hB, u, hu, smul_smul r B u⟩
    · refine ⟨(-r) * B, mul_nonneg (by linarith) hB, -u, hn u hu, ?_⟩
      simp only [neg_mul, neg_smul, smul_neg, neg_neg, smul_smul]

end Hindman168
