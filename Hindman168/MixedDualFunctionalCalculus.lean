import Hindman168.MixedDualHilbertRepresentatives
import Mathlib.Topology.ContinuousMap.Weierstrass

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

theorem mixedDualHilbert_polynomial_representative (hs : ∀ w, ∑ c, p w c = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (hf : ∀ w c, ∃ u ∈ subgroupMixedDualHull (Q w) d,
      (fun x => f.val w (c, x)) = B • u) (P : Polynomial ℝ) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      hilbertFamilyToCompletion _ U t ∈ Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) ∧
      ∀ w c x, t.val w (c, x) = P.eval (f.val w (c, x)) := by
  choose u hu he using hf
  have hpow (k w : ℕ) (c : κ w) : (fun x => u w c x ^ k) ∈ subgroupMixedDualHull (Q w) d := by
    induction k with
    | zero =>
      convert subgroupMixedDualHull_one_mem (Q w) d using 1
      funext x
      exact pow_zero _
    | succ k ih => simpa only [pow_succ, Pi.mul_def] using subgroupMixedDualHull_mul_mem (Q w) d ih (hu w c)
  let a := fun k => weightedHaarBoundedFamily p hs (fun w c x => u w c x ^ k) 1 zero_le_one
    (fun w c x => subgroupMixedDualHull_abs_le_one (Q w) d (hpow k w c) x)
  let t := ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k * B ^ k) • a k
  refine ⟨t, ?_, ?_⟩
  · change (hilbertFamilyCompletionLinearMap _ U) t ∈ _
    simp only [t, map_sum, map_smul]
    apply Submodule.sum_mem
    intro k _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a k, hpow k, rfl⟩
  · intro w c x
    simp only [t, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, a, weightedHaarBoundedFamily]
    change (∑ k ∈ Finset.range (P.natDegree + 1),
      (fun z : κ w × G w => (P.coeff k * B ^ k) * u w z.1 z.2 ^ k)) (c, x) = _
    simp only [Finset.sum_apply]
    change (∑ k ∈ Finset.range (P.natDegree + 1),
      (P.coeff k * B ^ k) * u w c x ^ k) = P.eval (f.val w (c, x))
    rw [Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hx : f.val w (c, x) = B * u w c x := congrFun (he w c) x
    rw [hx, mul_pow, mul_assoc]

omit Q d in
theorem weightedHaarHilbert_uniform_distance_le (hs : ∀ w, ∑ c, p w c = 1)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ε : ℝ) (hε : 0 ≤ ε) (hfg : ∀ w c x, |f.val w (c, x) - g.val w (c, x)| ≤ ε) :
    ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U g‖ ≤ ε := by
  change ‖(hilbertFamilyCompletionLinearMap _ U) f - (hilbertFamilyCompletionLinearMap _ U) g‖ ≤ ε
  rw [← map_sub]
  apply hilbertFamilyToCompletion_norm_le _ U (f - g) hε
  intro w
  exact finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ hε
    (fun z _ => hfg w z.1 z.2)

/-- Continuous scalar functions of a scaled-hull representative belong to the closed
dual subspace whenever their actual pointwise composition has a bounded family representative. -/
theorem mixedDualHilbert_continuous_comp_mem (hs : ∀ w, ∑ c, p w c = 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ w c, ∃ u ∈ subgroupMixedDualHull (Q w) d,
      (fun x => f.val w (c, x)) = B • u)
    (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Set.Icc (-B) B))
    (ht : ∀ w c x, t.val w (c, x) = ψ (f.val w (c, x))) :
    hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-B) B ψ hψ (ε / 2) (by positivity)
  obtain ⟨a, ha, hea⟩ := mixedDualHilbert_polynomial_representative p Q d U hs f B hf P
  refine ⟨hilbertFamilyToCompletion _ U a, ha, ?_⟩
  rw [dist_eq_norm]
  refine (weightedHaarHilbert_uniform_distance_le p U hs t a (ε / 2) (by positivity) ?_).trans_lt (by linarith)
  intro w c x
  obtain ⟨u, hu, he⟩ := hf w c
  have hb : |f.val w (c, x)| ≤ B := by
    have hx : f.val w (c, x) = B * u x := congrFun he x
    rw [hx, abs_mul, abs_of_nonneg hB]
    exact (mul_le_mul_of_nonneg_left (subgroupMixedDualHull_abs_le_one (Q w) d hu x) hB).trans_eq (mul_one B)
  rw [ht, hea, abs_sub_comm]
  exact (hP _ (abs_le.mp hb)).le

end Hindman168
