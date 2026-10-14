import Hindman168.WeightedBesselSampleLimit
import Hindman168.MixedDualFiniteGowersBessel

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- Qualitative Bessel in the weighted varying-index ultrafilter limit.
Vanishing original independent pair mean at degree 2d-1 forces vanishing
original mean of the degree-d norms. The index, group and cell types may
all vary without cardinality bounds, and both original laws are retained. -/
theorem mixedDualHilbert_weighted_bessel_tendsto_zero
    {G κ A : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)] [∀ w, Fintype (A w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)] (hs : ∀ w, ∑ c, p w c = 1)
    (α : ∀ w, A w → ℝ) (hα : ∀ w a, 0 ≤ α w a) (hαs : ∀ w, ∑ a, α w a = 1)
    (Q : ∀ w, A w → AddSubgroup (G w))
    [∀ w a, Fintype (Q w a)] [∀ w a b, Fintype (Q w a ⊔ Q w b : AddSubgroup (G w))]
    (d : ℕ) (hd : 0 < d) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hp : Tendsto (fun w => ∑ a, ∑ b, α w a * α w b *
      weightedSubgroupGowersValue (Q w a ⊔ Q w b) (p w) (d + d - 1)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    Tendsto (fun w => ∑ a, α w a * weightedSubgroupGowersValue (Q w a) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  let μ := fun w => Finsupp.onFinset (Finset.univ : Finset (A w)) (α w) (by simp)
  have hμ (w : ℕ) (a : A w) : 0 ≤ μ w a := hα w a
  have hμt (w : ℕ) : total (μ w) = 1 := by
    rw [total_eq_sum _ (Finset.subset_univ _)]
    exact hαs w
  have hE (w : ℕ) (f : A w → ℝ) : expectation (μ w) f = ∑ a, α w a * f a := by
    rw [expectation_eq_sum _ _ (Finset.subset_univ _)]
    rfl
  let l := fun w a => weightedSubgroupGowersValue (Q w a) (p w) d (fun c x => g.val w (c, x))
  let f := fun w a b => weightedSubgroupGowersValue (Q w a ⊔ Q w b) (p w) (d + d - 1)
    (fun c x => g.val w (c, x))
  have hl0 (w : ℕ) (a : A w) : 0 ≤ l w a :=
    weightedSubgroupGowersValue_nonneg (Q w a) (p w) Fact.out d hd _
  have hl1 (w : ℕ) (a : A w) : l w a ≤ 1 :=
    weightedSubgroupGowersValue_le_one (Q w a) (p w) Fact.out (hs w) d hd _ (hg w)
  have hlf (w : ℕ) (a : A w) : |l w a| ≤ 1 := by
    rw [abs_of_nonneg (hl0 w a)]
    exact hl1 w a
  have hf (w : ℕ) (a b : A w) : 0 ≤ f w a b :=
    weightedSubgroupGowersValue_nonneg (Q w a ⊔ Q w b) (p w) Fact.out
      (d + d - 1) (by omega) _
  have hpair : Tendsto (fun w => expectation (μ w) (fun a => expectation (μ w) (f w a)))
      (U : Filter ℕ) (𝓝 0) := by
    convert hp using 1
    funext w
    simp only [hE, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change α w a * (α w b * f w a b) = α w a * α w b * f w a b
    ring
  let t := fun w => ∑ a, α w a * l w a
  have ht0 (w : ℕ) : 0 ≤ t w := Finset.sum_nonneg (fun a _ => mul_nonneg (hα w a) (hl0 w a))
  have ht1 (w : ℕ) : t w ≤ 1 := by
    calc
      _ ≤ ∑ a, α w a * 1 := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hl1 w a) (hα w a))
      _ = _ := by simpa only [mul_one] using hαs w
  have htl := bounded_real_ultrafilter_tendsto U t ⟨1, zero_le_one,
    fun w => by rw [abs_of_nonneg (ht0 w)]; exact ht1 w⟩
  let a := limUnder (U : Filter ℕ) t
  have ha : 0 ≤ a := ge_of_tendsto htl (Eventually.of_forall ht0)
  have haz : a = 0 := by
    by_contra hnz
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hnz)
    have hh : 0 < min ((a / 2) ^ (2 ^ d)) ((a / 2) ^ 2 / 2) := by positivity
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hh
    let m := n + 1
    have hm : 0 < m := Nat.succ_pos n
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have hsmall1 : 1 / (m : ℝ) < (a / 2) ^ (2 ^ d) := by
      simpa only [m, Nat.cast_add, Nat.cast_one] using hn.trans_le (min_le_left _ _)
    have hsmall2 : 2 / (m : ℝ) < (a / 2) ^ 2 := by
      have h := hn.trans_le (min_le_right _ _)
      have h' : 1 / (m : ℝ) < (a / 2) ^ 2 / 2 := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using h
      have h'' := mul_lt_mul_of_pos_left h' (by norm_num : (0 : ℝ) < 2)
      have he : 2 * (1 / (m : ℝ)) = 2 / (m : ℝ) := by ring
      rw [he] at h''
      nlinarith
    obtain ⟨s, hmean, hzero⟩ := weighted_bessel_exists_sample_limit μ hμ hμt l hlf f hf
      U hU hpair m hm
    let Qs := fun (i : Fin m) w => Q w (s w i)
    obtain ⟨b, _, _, hbl, hbp⟩ := mixedDualHilbert_finite_gowers_bessel_limit
      p U Qs hU hs d hd g hg hzero
    have hbs : b ^ (2 ^ d) ≤ 1 / (m : ℝ) := by simpa only [Fintype.card_fin] using hbp
    have hbhalf : b < a / 2 :=
      lt_of_pow_lt_pow_left₀ (2 ^ d) (by positivity) (hbs.trans_lt hsmall1)
    have hdiff : (b - a) ^ 2 ≤ 2 / (m : ℝ) := by
      apply le_of_tendsto ((hbl.sub htl).pow 2)
      apply Eventually.of_forall
      intro w
      simpa only [hE] using hmean w
    have hgap : a / 2 < a - b := by linarith
    have hbig : (a / 2) ^ 2 < (b - a) ^ 2 := by
      rw [sub_sq_comm]
      exact (sq_lt_sq₀ (by positivity : 0 ≤ a / 2) (by linarith : 0 ≤ a - b)).mpr hgap
    exact (not_lt_of_ge hdiff) (hsmall2.trans hbig)
  change Tendsto t (U : Filter ℕ) (𝓝 0)
  change Tendsto t (U : Filter ℕ) (𝓝 a) at htl
  rwa [haz] at htl

end Hindman168
