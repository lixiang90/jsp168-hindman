import Hindman168.MixedCubeProjectionLimit
import Hindman168.MixedDualSignedExactModel
import Hindman168.SubgroupCubeL2Energy

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- The limiting genuine Gowers dyadic power is bounded by the squared
norm of the genuine factor projection, with the original cell weights.
The proof replaces all actual vertices by a signed unit model. -/
theorem mixedDualHilbert_gowers_power_le_projection_energy
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 a) ∧
      a ^ (2 ^ d) ≤ ‖(mixedDualHilbertSubspace p Q d U).starProjection
        (hilbertFamilyToCompletion _ U g)‖ ^ 2 := by
  obtain ⟨a, ha, haone, ht, _⟩ := mixedDualHilbert_gowers_power_le_projection p Q d U hs hd g hg
  obtain ⟨q, hq, hrep⟩ := mixedDualHilbert_projection_signed_exact_representative p Q d U hU hs hd g hg
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let V := mixedDualHilbertSubspace p Q d U
  have ho : H (g - q) ∈ Vᗮ := by
    rw [H.map_sub]
    change H g - hilbertFamilyToCompletion _ U q ∈ Vᗮ
    rw [hrep]
    exact V.sub_starProjection_mem_orthogonal _
  have hr := mixedDualHilbert_cube_projection_replacement_tendsto_zero p Q d U hs
    (fun _ => g) (fun _ => q) (fun _ => hg) (fun _ => hq) (fun _ => ho)
  have hp : Tendsto (fun w => weightedSubgroupCubeAverage (p w) (Q w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 (a ^ (2 ^ d))) := by
    simpa only [weightedSubgroupGowersValue_pow _ _ (Fact.out : ∀ c, 0 ≤ p _ c) d hd,
      subgroupGowersValue_pow _ d hd, weightedSubgroupCubeAverage] using ht.pow (2 ^ d)
  change Tendsto (fun w => weightedSubgroupCubeAverage (p w) (Q w) d
      (fun c x => g.val w (c, x)) - weightedSubgroupCubeAverage (p w) (Q w) d
      (fun c x => q.val w (c, x))) (U : Filter ℕ) (𝓝 0) at hr
  have hqc : Tendsto (fun w => weightedSubgroupCubeAverage (p w) (Q w) d
      (fun c x => q.val w (c, x))) (U : Filter ℕ) (𝓝 (a ^ (2 ^ d))) := by
    have hh := hp.sub hr
    simpa only [sub_sub_cancel, sub_zero] using hh
  have hqe : Tendsto (fun w => ∑ c, p w c * finiteHaarMean
      (fun x => q.val w (c, x) ^ 2)) (U : Filter ℕ)
      (𝓝 (‖(mixedDualHilbertSubspace p Q d U).starProjection
        (hilbertFamilyToCompletion _ U g)‖ ^ 2)) := by
    have hh := weightedHaarHilbert_inner_tendsto p U q q
    rw [hrep, real_inner_self_eq_norm_sq] at hh
    simpa only [pow_two] using hh
  refine ⟨a, ha, haone, ht, ?_⟩
  exact le_of_tendsto_of_tendsto hqc hqe (Eventually.of_forall (fun w =>
    weightedSubgroupCubeAverage_le_L2_energy (Q w) (p w) Fact.out d hd _ (hq w)))

end Hindman168
