import Hindman168.MixedDualFiniteBesselEnergy
import Hindman168.MixedDualGowersProjectionEnergy

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] {ι : Type*} [Fintype ι]
  (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (Q : ι → ∀ w, AddSubgroup (G w))
  [∀ i w, Fintype (Q i w)] [∀ i j w, Fintype (Q i w ⊔ Q j w : AddSubgroup (G w))]

/-- The genuine limiting Gowers powers of a fixed finite family sum to
at most one when all off-diagonal concatenated norms vanish. Different
positive degrees are allowed, and no diagonal vanishing is assumed. -/
theorem mixedDualHilbert_finite_gowers_bessel_powers
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hz : ∀ i j, i ≠ j → Tendsto (fun w =>
      weightedSubgroupGowersValue (Q i w ⊔ Q j w) (p w) (d i + d j - 1)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1 ∧
      Tendsto (fun w => weightedSubgroupGowersValue (Q i w) (p w) (d i)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 (a i))) ∧
      ∑ i, a i ^ (2 ^ d i) ≤ 1 := by
  choose a ha haone ht hpow using (fun i =>
    mixedDualHilbert_gowers_power_le_projection_energy p (Q i) (d i) U hU hs (hd i) g hg)
  refine ⟨a, fun i => ⟨ha i, haone i, ht i⟩, ?_⟩
  exact (Finset.sum_le_sum (fun i _ => hpow i)).trans
    (mixedDualHilbert_finite_bessel_energy_le_one p U Q hU hs d hd g hg hz)

/-- Fixed-family qualitative Bessel in the limit, with the same dyadic
power as the paper. Its bound depends only on the number of sampled
directions and the order, retaining all original cell probabilities. -/
theorem mixedDualHilbert_finite_gowers_bessel_average [Nonempty ι]
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d : ℕ) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hz : ∀ i j, i ≠ j → Tendsto (fun w =>
      weightedSubgroupGowersValue (Q i w ⊔ Q j w) (p w) (d + d - 1)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1 ∧
      Tendsto (fun w => weightedSubgroupGowersValue (Q i w) (p w) d
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 (a i))) ∧
      finiteHaarMean a ^ (2 ^ d) ≤ 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨a, ha, hb⟩ := mixedDualHilbert_finite_gowers_bessel_powers p U Q hU hs
    (fun _ => d) (fun _ => hd) g hg hz
  refine ⟨a, ha, (finiteHaarMean_pow_two_pow_le a d).trans ?_⟩
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)

/-- Aggregate form for the actual stagewise mean of the Gowers values.
The same ultrafilter limit exists and has dyadic power at most 1/M. -/
theorem mixedDualHilbert_finite_gowers_bessel_limit [Nonempty ι]
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d : ℕ) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hz : ∀ i j, i ≠ j → Tendsto (fun w =>
      weightedSubgroupGowersValue (Q i w ⊔ Q j w) (p w) (d + d - 1)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧
      Tendsto (fun w => finiteHaarMean (fun i => weightedSubgroupGowersValue
        (Q i w) (p w) d (fun c x => g.val w (c, x)))) (U : Filter ℕ) (𝓝 b) ∧
      b ^ (2 ^ d) ≤ 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨a, ha, hb⟩ := mixedDualHilbert_finite_gowers_bessel_average p U Q hU hs d hd g hg hz
  refine ⟨finiteHaarMean a, finiteHaarMean_nonneg a (fun i => (ha i).1), ?_, ?_, hb⟩
  · exact (finiteHaarMean_mono a (fun _ => (1 : ℝ)) (fun i => (ha i).2.1)).trans_eq
      (finiteHaarMean_const _)
  · have ht := (tendsto_finsetSum Finset.univ (fun i _ => (ha i).2.2)).div_const
      (Fintype.card ι : ℝ)
    simpa only [finiteHaarMean] using ht

end Hindman168
