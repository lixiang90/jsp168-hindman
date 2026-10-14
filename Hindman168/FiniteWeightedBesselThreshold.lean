import Hindman168.FiniteWeightedSubgroupSystem
import Hindman168.MixedDualWeightedBesselLimit

namespace Hindman168
open Filter
open scoped BigOperators Classical Topology
universe u

/-- The already proved weighted Bessel limit applies to sequences of
arbitrary bundled finite systems, including changing all three types. -/
theorem finiteWeightedSubgroup_bessel_null_limit
    (S : ℕ → FiniteWeightedSubgroupSystem)
    (d : ℕ) (hd : 0 < d) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (hp : Tendsto (fun w => finiteWeightedSubgroupPairMean (S w) (d + d - 1))
      (U : Filter ℕ) (𝓝 0)) :
    Tendsto (fun w => finiteWeightedSubgroupMean (S w) d) (U : Filter ℕ) (𝓝 0) := by
  let p := fun w => (S w).p
  letI : ∀ w, AddCommGroup (S w).G := fun w => (S w).addCommGroup
  letI : ∀ w, Fintype (S w).G := fun w => (S w).finiteGroup
  letI : ∀ w, Fintype (S w).κ := fun w => (S w).finiteCells
  letI : ∀ w, Fintype (S w).A := fun w => (S w).finiteIndices
  letI : ∀ w, Fact (∀ c, 0 ≤ p w c) := fun w => ⟨(S w).p_nonneg⟩
  letI : ∀ w a, Fintype ((S w).Q a) := fun _ _ => inferInstance
  letI : ∀ w a b, Fintype ((S w).Q a ⊔ (S w).Q b : AddSubgroup (S w).G) :=
    fun _ _ _ => inferInstance
  let g := weightedHaarBoundedFamily p (fun w => (S w).p_total)
    (fun w => (S w).g) 1 zero_le_one (fun w => (S w).g_unit)
  exact mixedDualHilbert_weighted_bessel_tendsto_zero p (fun w => (S w).p_total)
    (fun w => (S w).α) (fun w => (S w).α_nonneg) (fun w => (S w).α_total)
    (fun w => (S w).Q) d hd U hU g (fun w => (S w).g_unit) hp

/-- A single positive threshold works for every actual finite weighted
subgroup system. It depends only on the degree and required error, not
on any finite type, group law, subgroup family, weights or input. -/
theorem finiteWeightedSubgroup_bessel_uniform_threshold
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : FiniteWeightedSubgroupSystem.{u},
      finiteWeightedSubgroupPairMean S (d + d - 1) ≤ δ →
        finiteWeightedSubgroupMean S d < ε := by
  by_contra hn
  have hbad (n : ℕ) : ∃ S : FiniteWeightedSubgroupSystem.{u},
      finiteWeightedSubgroupPairMean S (d + d - 1) ≤ 1 / ((n : ℝ) + 1) ∧
        ε ≤ finiteWeightedSubgroupMean S d := by
    have hnot : ¬∀ S : FiniteWeightedSubgroupSystem.{u},
        finiteWeightedSubgroupPairMean S (d + d - 1) ≤ 1 / ((n : ℝ) + 1) →
          finiteWeightedSubgroupMean S d < ε := by
      intro h
      exact hn ⟨1 / ((n : ℝ) + 1), by positivity, h⟩
    push Not at hnot
    exact hnot
  choose S hpair hlarge using hbad
  have hp : Tendsto (fun n => finiteWeightedSubgroupPairMean (S n) (d + d - 1))
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun n =>
      finiteWeightedSubgroupPairMean_nonneg (S n) _ (by omega)))
      (Eventually.of_forall hpair)
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left Nat.hyperfilter_le_atTop)
  have hz := finiteWeightedSubgroup_bessel_null_limit S d hd (hyperfilter ℕ)
    Nat.hyperfilter_le_atTop hp
  obtain ⟨n, hn⟩ := (hz.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge (hlarge n)) hn

end Hindman168
