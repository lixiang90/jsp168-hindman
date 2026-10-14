import Hindman168.NestedMixedDualCorrelationLimit
import Hindman168.NestedMixedDualDensity

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (Q R : ∀ w, AddSubgroup (G w))
  [∀ w, Fintype (Q w)] [∀ w, Fintype (R w)]
  [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))] (d e k : ℕ)
  (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hk : 0 < k)
  (hleft : 0 < d → mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R (e + 1) U ≤
    mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) k U)
  (hright : 0 < e → mixedDualHilbertSubspace p R e U ⊓ mixedDualHilbertSubspace p Q (d + 1) U ≤
    mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) k U)

include hU hs hk hleft hright

/-- Null correlation of every genuine nested generator with actual unit
tests whose next-order subgroup-sum Gowers value vanishes. -/
theorem nestedMixedDualFamily_inner_zero
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : f ∈ nestedMixedDualFamilies p Q (d + 1) U R (e + 1) {0})
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hzero : Tendsto (fun w => weightedSubgroupGowersValue (Q w ⊔ R w) (p w) (k + 1)
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    inner ℝ (hilbertFamilyToCompletion _ U f) (hilbertFamilyToCompletion _ U g) = 0 := by
  obtain ⟨v, hvunit, hv, hr, hfval⟩ := hf
  obtain ⟨u, huunit, hu, hroot⟩ := hr
  have ht := mixedDualHilbert_nested_correlation_tendsto_zero p hs U hU Q R d e k hk
    hleft hright v u (fun ω _ => hvunit ω) (fun ω _ => huunit ω)
    (fun ω hω => (hv ω hω).2) (fun ω hω => (hu ω hω).2) hroot g hg hzero
  have hi := weightedHaarHilbert_inner_tendsto p U f g
  simp only [hfval] at hi
  exact tendsto_nhds_unique hi ht

/-- The exact unit-interval target projection produces a unit residual.
The null-correlation theorem forces that residual to vanish, placing the
whole genuine nested generator in the target closed dual space. -/
theorem nestedMixedDualFamily_mem_sum
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : f ∈ nestedMixedDualFamilies p Q (d + 1) U R (e + 1) {0}) :
    hilbertFamilyToCompletion _ U f ∈
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (k + 1) U := by
  let V := mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (k + 1) U
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => (1 : ℝ))
    1 zero_le_one (by simp)
  have hone : H one ∈ V := (Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (Q w ⊔ R w) (k + 1), rfl⟩)
  have hfunit := nestedMixedDualFamily_unit p Q (d + 1) U R (e + 1) {0} hf
  let plus := (1 / 2 : ℝ) • (f + one)
  have hplus : ∀ w c x, 0 ≤ plus.val w (c, x) ∧ plus.val w (c, x) ≤ 1 := by
    intro w c x
    have hb := abs_le.mp (hfunit w c x)
    change 0 ≤ (1 / 2 : ℝ) * (f.val w (c, x) + 1) ∧
      (1 / 2 : ℝ) * (f.val w (c, x) + 1) ≤ 1
    constructor <;> linarith
  obtain ⟨t, htunit, ht⟩ := mixedDualHilbert_projection_exact_representative p
    (fun w => Q w ⊔ R w) (k + 1) U hU hs (Nat.succ_pos _) plus hplus
  change H t = V.starProjection (H plus) at ht
  have htm : H t ∈ V := ht ▸ V.starProjection_apply_mem (H plus)
  let g := plus - t
  have hgun : ∀ w c x, |g.val w (c, x)| ≤ 1 := by
    intro w c x
    change |plus.val w (c, x) - t.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hplus w c x).1, (htunit w c x).2],
      by linarith [(hplus w c x).2, (htunit w c x).1]⟩
  have hgo : H g ∈ Vᗮ := by
    change H (plus - t) ∈ Vᗮ
    rw [H.map_sub, ht]
    exact V.sub_starProjection_mem_orthogonal _
  have hz := mixedDualHilbert_gowers_zero_of_orthogonal p (fun w => Q w ⊔ R w) (k + 1)
    U hs (Nat.succ_pos _) g hgun hgo
  have hif : inner ℝ (H f) (H g) = 0 :=
    nestedMixedDualFamily_inner_zero p U Q R d e k hU hs hk hleft hright f hf g hgun hz
  have hione : inner ℝ (H one) (H g) = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hgo _ hone
  have hip : inner ℝ (H plus) (H g) = 0 := by
    change inner ℝ (H ((1 / 2 : ℝ) • (f + one))) (H g) = 0
    rw [H.map_smul, H.map_add, inner_smul_left, inner_add_left, hif, hione]
    simp only [add_zero, mul_zero]
  have hit : inner ℝ (H t) (H g) = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hgo _ htm
  have hig : inner ℝ (H g) (H g) = inner ℝ (H plus - H t) (H g) :=
    congrArg (fun z => inner ℝ z (H g)) (H.map_sub plus t)
  rw [inner_sub_left, hip, hit, sub_self] at hig
  have hgzero : H g = 0 := inner_self_eq_zero.mp hig
  have heq : H plus = H t := sub_eq_zero.mp (by
    rw [← H.map_sub]
    exact hgzero)
  have hpm : H plus ∈ V := by rw [heq]; exact htm
  have hfrep : f = (2 : ℝ) • plus - one := by
    apply Subtype.ext
    funext w z
    change f.val w z = 2 * ((1 / 2 : ℝ) * (f.val w z + 1)) - 1
    ring
  change H f ∈ V
  rw [hfrep, H.map_sub, H.map_smul]
  exact V.sub_mem (V.smul_mem _ hpm) hone

/-- The full completed-Hilbert-space concatenation step, with exactly the
two lower-order containments to be discharged by strong induction. -/
theorem mixedDualHilbert_concatenation_step :
    mixedDualHilbertSubspace p Q (d + 1) U ⊓ mixedDualHilbertSubspace p R (e + 1) U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (k + 1) U := by
  rw [← nestedMixedDualHilbertSubspace_eq_intersection p Q (d + 1) U R (e + 1) {0}
    hU hs (Nat.succ_pos _) (Nat.succ_pos _) (by simp)]
  apply (Submodule.span ℝ (nestedMixedDualHilbertGenerators p Q (d + 1) U R (e + 1) {0})).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro z ⟨f, hf, rfl⟩
    exact nestedMixedDualFamily_mem_sum p U Q R d e k hU hs hk hleft hright f hf
  · exact (Submodule.span ℝ (mixedDualHilbertGenerators p (fun w => Q w ⊔ R w) (k + 1) U)).isClosed_topologicalClosure

end Hindman168
