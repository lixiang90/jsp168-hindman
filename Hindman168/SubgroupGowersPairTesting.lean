import Hindman168.SubgroupCubePairDerivative
import Mathlib.Topology.Algebra.Order.Field

/-! A small-test bound and a Markov estimate control the mean absolute
correlation by the genuine next-order Gowers moment. -/
namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem finiteHaarMean_abs_le_of_power_threshold {A : Type*}
    [Fintype A] [Nonempty A] (N r : A → ℝ) (hN : ∀ a, 0 ≤ N a)
    (hr : ∀ a, |r a| ≤ 1) (q : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hsmall : ∀ a, N a ≤ δ → |r a| ≤ ε) :
    finiteHaarMean (fun a => |r a|) ≤
      ε + finiteHaarMean (fun a => N a ^ q) / δ ^ q := by
  have hpow : 0 < δ ^ q := pow_pos hδ q
  have hpoint (a : A) : |r a| ≤ ε + N a ^ q / δ ^ q := by
    by_cases ha : N a ≤ δ
    · exact (hsmall a ha).trans (le_add_of_nonneg_right
        (div_nonneg (pow_nonneg (hN a) q) (le_of_lt hpow)))
    · have hratio : (1 : ℝ) ≤ N a ^ q / δ ^ q := by
        apply (le_div_iff₀ hpow).mpr
        simpa only [one_mul] using pow_le_pow_left₀ (le_of_lt hδ) (le_of_not_ge ha) q
      exact (hr a).trans (hratio.trans (le_add_of_nonneg_left hε))
  calc
    _ ≤ finiteHaarMean (fun a => ε + N a ^ q / δ ^ q) :=
      finiteHaarMean_mono _ _ hpoint
    _ = _ := by
      rw [finiteHaarMean_add, finiteHaarMean_const]
      simp only [div_eq_mul_inv, finiteHaarMean_mul_const]

theorem weightedSubgroupGowersValue_pair_test_bound
    {G κ : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q : AddSubgroup G) [Fintype Q] (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c)
    (d : ℕ) (hd : 0 < d) (h : κ → G → ℝ) (r : Q → Q → ℝ)
    (hr : ∀ a b, |r a b| ≤ 1) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hsmall : ∀ (a b : Q), weightedSubgroupGowersValue Q p d
      (fun c x => h c (x + a) * h c (x + b)) ≤ δ → |r a b| ≤ ε) :
    finiteHaarMean (fun a : Q => finiteHaarMean (fun b : Q => |r a b|)) ≤
      ε + weightedSubgroupGowersValue Q p (d + 1) h ^ (2 ^ (d + 1)) / δ ^ (2 ^ d) := by
  have hb (a : Q) := finiteHaarMean_abs_le_of_power_threshold
    (fun b : Q => weightedSubgroupGowersValue Q p d
      (fun c x => h c (x + a) * h c (x + b))) (r a)
    (fun b => weightedSubgroupGowersValue_nonneg Q p hp d hd _) (hr a)
    (2 ^ d) ε δ hε hδ (hsmall a)
  calc
    _ ≤ finiteHaarMean (fun a : Q => ε + finiteHaarMean (fun b : Q =>
        weightedSubgroupGowersValue Q p d
          (fun c x => h c (x + a) * h c (x + b)) ^ (2 ^ d)) / δ ^ (2 ^ d)) :=
      finiteHaarMean_mono _ _ hb
    _ = _ := by
      rw [finiteHaarMean_add, finiteHaarMean_const]
      simp only [div_eq_mul_inv, finiteHaarMean_mul_const]
      rw [weightedSubgroupGowersValue_pair_moment Q p hp d hd h]

theorem weightedSubgroupGowersValue_pair_test_tendsto_zero
    {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)] (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)]
    (p : ∀ w, κ w → ℝ) (hp : ∀ w c, 0 ≤ p w c) (d : ℕ) (hd : 0 < d)
    (h : ∀ w, κ w → G w → ℝ) (r : ∀ w, Q w → Q w → ℝ)
    (hr : ∀ w a b, |r w a b| ≤ 1) (L : Filter ℕ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in L,
      ∀ (a b : Q w), weightedSubgroupGowersValue (Q w) (p w) d
        (fun c x => h w c (x + a) * h w c (x + b)) ≤ δ → |r w a b| ≤ ε)
    (hzero : Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) (d + 1) (h w))
      L (𝓝 0)) :
    Tendsto (fun w => finiteHaarMean (fun a : Q w =>
      finiteHaarMean (fun b : Q w => |r w a b|))) L (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := hsmall (ε / 2) (by positivity)
  have hm : Tendsto (fun w =>
      weightedSubgroupGowersValue (Q w) (p w) (d + 1) (h w) ^ (2 ^ (d + 1)) /
        δ ^ (2 ^ d)) L (𝓝 0) := by
    have htend := (hzero.pow (2 ^ (d + 1))).div_const (δ ^ (2 ^ d))
    simpa only [zero_pow (by positivity : (2 ^ (d + 1) : ℕ) ≠ 0), zero_div] using htend
  have hlt := hm.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [ht, hlt] with w hw hmw
  have hb := weightedSubgroupGowersValue_pair_test_bound
    (Q w) (p w) (hp w) d hd (h w) (r w) (hr w) (ε / 2) δ
    (by positivity) hδ hw
  have hn : 0 ≤ finiteHaarMean (fun a : Q w => finiteHaarMean (fun b : Q w => |r w a b|)) :=
    finiteHaarMean_nonneg _ (fun a => finiteHaarMean_nonneg _ (fun b => abs_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith

end Hindman168
