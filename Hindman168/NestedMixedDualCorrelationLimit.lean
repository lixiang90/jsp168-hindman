import Hindman168.NestedMixedDualCorrelation
import Hindman168.NestedMixedDualUniformThreshold

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- The exact nested expansion, uniform paired-coefficient threshold and
sum-subgroup moment imply null correlation against every unit test with
vanishing next-order Gowers value. The lower containments remain explicit. -/
theorem mixedDualHilbert_nested_correlation_tendsto_zero
    {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (Q R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] [∀ w, Fintype (R w)]
    [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))] (d e k : ℕ) (hk : 0 < k)
    (hleft : 0 < d → mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R (e + 1) U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) k U)
    (hright : 0 < e → mixedDualHilbertSubspace p R e U ⊓ mixedDualHilbertSubspace p Q (d + 1) U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) k U)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (u : Finset (Fin (e + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hfunit : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (huunit : ∀ ω, ω ≠ ∅ → ∀ w c x, |(u ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R (e + 1) U)
    (hu : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (u ω) ∈ mixedDualHilbertSubspace p Q (d + 1) U)
    (hroot : ∀ w c y, (f {0}).val w (c, y) = subgroupMixedDualFunction (R w) (e + 1)
      (fun ω x => (u ω).val w (c, x)) y)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hzero : Tendsto (fun w => weightedSubgroupGowersValue (Q w ⊔ R w) (p w) (k + 1)
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    Tendsto (fun w => ∑ c, p w c * finiteHaarMean (fun x =>
      subgroupMixedDualFunction (Q w) (d + 1) (fun ω y => (f ω).val w (c, y)) x *
        g.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  have ht := mixedDualHilbert_nested_pair_gowers_threshold p hs U hU Q R d e
    (fun w => Q w ⊔ R w) k hk hleft hright f u hfunit huunit hf hu
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, htest⟩ := ht (ε ^ 2 / 2) (by positivity)
  have hm : Tendsto (fun w => weightedSubgroupGowersValue (Q w ⊔ R w) (p w) (k + 1)
      (fun c x => g.val w (c, x)) ^ (2 ^ (k + 1)) / δ ^ (2 ^ k)) (U : Filter ℕ) (𝓝 0) := by
    have hm' := (hzero.pow (2 ^ (k + 1))).div_const (δ ^ (2 ^ k))
    simpa only [zero_pow (by positivity : (2 ^ (k + 1) : ℕ) ≠ 0), zero_div] using hm'
  have hlt := hm.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 2 by positivity))
  filter_upwards [htest, hlt] with w hw hmw
  have hb := weightedHaar_nested_dual_correlation_bound (Q w) (R w) (p w) (Fact.out : ∀ c, 0 ≤ p w c)
    (hs w) d e k hk (fun c ω y => (f ω).val w (c, y))
    (fun c ω y => (u ω).val w (c, y)) (fun c x => g.val w (c, x))
    (fun c ω hω y => hfunit ω hω w c y) (fun c ω hω y => huunit ω hω w c y)
    (hg w) (hroot w) (ε ^ 2 / 2) δ (by positivity) hδ
  have hsmall : ∀ (b a a' : Q w × R w), weightedSubgroupGowersValue (Q w ⊔ R w) (p w) k
      (fun c x => g.val w (c, x + ((a.1 : G w) + a.2)) *
        g.val w (c, x + ((a'.1 : G w) + a'.2))) ≤ δ →
      |∑ c, p w c * finiteHaarMean (fun x =>
        subgroupNestedMixedDualCoefficient (Q w) (R w) d e
          (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y)) a.1 a.2 b.1 b.2 x *
        subgroupNestedMixedDualCoefficient (Q w) (R w) d e
          (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y)) a'.1 a'.2 b.1 b.2 x *
          (g.val w (c, x + ((a.1 : G w) + a.2)) * g.val w (c, x + ((a'.1 : G w) + a'.2))))| ≤ ε ^ 2 / 2 := by
    intro b a a' hz
    let n : Fin 2 → κ w → G w := ![fun _ => a.1, fun _ => a'.1]
    let m : Fin 2 → κ w → G w := ![fun _ => a.2, fun _ => a'.2]
    let h : Fin 2 → κ w → G w := fun _ _ => b.1
    let j : Fin 2 → κ w → G w := fun _ _ => b.2
    let D := fun c x => g.val w (c, x + ((a.1 : G w) + a.2)) *
      g.val w (c, x + ((a'.1 : G w) + a'.2))
    have hD : ∀ c x, |D c x| ≤ 1 := by
      intro c x
      rw [abs_mul]
      exact (mul_le_mul (hg w c _) (hg w c _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hc := (hw n m h j D hD hz).le
    apply le_trans (le_of_eq ?_) hc
    apply congrArg abs
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    congr 1
    funext x
    rw [Fin.prod_univ_two]
    dsimp only [n, m, h, j, D]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsquare := hb hsmall
  rw [Real.dist_eq, sub_zero]
  apply (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hε)).mp
  rw [sq_abs]
  nlinarith

end Hindman168
