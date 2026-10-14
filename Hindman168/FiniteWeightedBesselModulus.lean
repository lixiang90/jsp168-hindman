import Hindman168.FiniteWeightedBesselThreshold

namespace Hindman168
open Filter
open scoped Classical Topology

/-- All possible degree-d local means at a given pair-mean budget,
together with zero. All finite systems of ordinary small types are included. -/
def finiteWeightedBesselValues (d : ℕ) (δ : ℝ) : Set ℝ :=
  {r | r = 0 ∨ ∃ S : FiniteWeightedSubgroupSystem.{0},
    finiteWeightedSubgroupPairMean S (d + d - 1) ≤ δ ∧
      r = finiteWeightedSubgroupMean S d}

/-- A monotone qualitative modulus defined over all finite systems,
without any fixed cardinality, group, direction or cell parameters. -/
noncomputable def finiteWeightedBesselModulus (d : ℕ) (δ : ℝ) : ℝ :=
  sSup (finiteWeightedBesselValues d δ)

theorem finiteWeightedBesselValues_bddAbove (d : ℕ) (hd : 0 < d) (δ : ℝ) :
    BddAbove (finiteWeightedBesselValues d δ) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with hzero | ⟨S, _, rfl⟩
  · simpa only [hzero] using (zero_le_one : (0 : ℝ) ≤ 1)
  · exact finiteWeightedSubgroupMean_le_one S d hd

theorem finiteWeightedBesselModulus_nonneg (d : ℕ) (hd : 0 < d) (δ : ℝ) :
    0 ≤ finiteWeightedBesselModulus d δ :=
  le_csSup (finiteWeightedBesselValues_bddAbove d hd δ) (Or.inl rfl)

theorem finiteWeightedBesselModulus_le_one (d : ℕ) (hd : 0 < d) (δ : ℝ) :
    finiteWeightedBesselModulus d δ ≤ 1 := by
  apply csSup_le (s := finiteWeightedBesselValues d δ) ⟨0, Or.inl rfl⟩
  intro r hr
  rcases hr with hzero | ⟨S, _, rfl⟩
  · simpa only [hzero] using (zero_le_one : (0 : ℝ) ≤ 1)
  · exact finiteWeightedSubgroupMean_le_one S d hd

theorem finiteWeightedBesselModulus_monotone (d : ℕ) (hd : 0 < d) :
    Monotone (finiteWeightedBesselModulus d) := by
  intro δ η hδη
  apply csSup_le_csSup (finiteWeightedBesselValues_bddAbove d hd η) ⟨0, Or.inl rfl⟩
  intro r hr
  rcases hr with hzero | ⟨S, hp, he⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨S, hp.trans hδη, he⟩

/-- The modulus controls the original weighted local mean whenever the
original independent pair mean fits the supplied budget. -/
theorem finiteWeightedSubgroupMean_le_besselModulus
    (S : FiniteWeightedSubgroupSystem.{0}) (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hp : finiteWeightedSubgroupPairMean S (d + d - 1) ≤ δ) :
    finiteWeightedSubgroupMean S d ≤ finiteWeightedBesselModulus d δ :=
  le_csSup (finiteWeightedBesselValues_bddAbove d hd δ) (Or.inr ⟨S, hp, rfl⟩)

theorem finiteWeightedBesselModulus_uniform_small (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≤ δ → finiteWeightedBesselModulus d t < ε := by
  obtain ⟨δ, hδ, hb⟩ := finiteWeightedSubgroup_bessel_uniform_threshold d hd
    (ε / 2) (by positivity)
  have hbound : finiteWeightedBesselModulus d δ ≤ ε / 2 := by
    apply csSup_le (s := finiteWeightedBesselValues d δ) ⟨0, Or.inl rfl⟩
    intro r hr
    rcases hr with hzero | ⟨S, hp, rfl⟩
    · rw [hzero]
      positivity
    · exact (hb S hp).le
  refine ⟨δ, hδ, fun t ht => ?_⟩
  exact ((finiteWeightedBesselModulus_monotone d hd ht).trans hbound).trans_lt
    (by linarith)

/-- The universal nondecreasing modulus tends to zero as the pair
budget tends to zero. This includes the positive one-sided limit. -/
theorem finiteWeightedBesselModulus_tendsto_zero (d : ℕ) (hd : 0 < d) :
    Tendsto (finiteWeightedBesselModulus d) (𝓝 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := finiteWeightedBesselModulus_uniform_small d hd ε hε
  filter_upwards [eventually_lt_nhds hδ] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg
    (finiteWeightedBesselModulus_nonneg d hd t)] using hb t ht.le

end Hindman168
