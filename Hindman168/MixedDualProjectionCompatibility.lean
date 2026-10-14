import Hindman168.MixedDualInternalLocalization

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- Relative orthogonality transfers through the first projection whenever its
output has an actual unit-bounded representative. -/
theorem mixedDualHilbert_projected_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (g t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (htunit : ∀ w c x, |t.val w (c, x)| ≤ 1)
    (ht : hilbertFamilyToCompletion _ U t =
      (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U g))
    (hg : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p R e U)ᗮ) :
    hilbertFamilyToCompletion _ U t ∈ (mixedDualHilbertSubspace p R e U)ᗮ := by
  apply mixedDualHilbert_relative_orthogonal p Q d U hs hd R e he t htunit
  · rw [ht]
    exact Submodule.starProjection_apply_mem _ _
  · rw [Submodule.mem_orthogonal']
    intro z hz
    rw [ht, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hz.1]
    exact (Submodule.mem_orthogonal' _ _).mp hg z hz.2

/-- On unit-interval actual inputs from the second dual space, the first
projection stays in that space. No commutation is assumed. -/
theorem mixedDualHilbert_projection_mem_other
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1)
    (hW : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p R e U) :
    (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) ∈
      mixedDualHilbertSubspace p R e U := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  obtain ⟨t, htunit, ht⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd f hf
  obtain ⟨s, hsunit, hseq⟩ := mixedDualHilbert_projection_exact_representative p R e U hU hs he t htunit
  obtain ⟨u, huunit, hueq⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd s hsunit
  change H t = V.starProjection (H f) at ht
  change H s = W.starProjection (H t) at hseq
  change H u = V.starProjection (H s) at hueq
  have htm : H t ∈ V := ht ▸ Submodule.starProjection_apply_mem V (H f)
  have hr : H (t - s) ∈ Wᗮ := by
    rw [H.map_sub, hseq]
    exact W.sub_starProjection_mem_orthogonal _
  have htu : ∀ w c x, |(t - u).val w (c, x)| ≤ 1 := by
    intro w c x
    change |t.val w (c, x) - u.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(htunit w c x).1, (huunit w c x).2],
      by linarith [(htunit w c x).2, (huunit w c x).1]⟩
  have heq : H (t - u) = V.starProjection (H (t - s)) := by
    rw [H.map_sub, H.map_sub, map_sub, ← hueq, Submodule.starProjection_eq_self_iff.mpr htm]
  have hpr : H (t - u) ∈ Wᗮ :=
    mixedDualHilbert_projected_orthogonal p Q d U hs hd R e he (t - s) (t - u) htu heq hr
  have hzero : inner ℝ (H t) (H (t - s)) = 0 := by
    rw [ht, Submodule.inner_starProjection_left_eq_right, ← heq]
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hpr _ hW
  have hszero : inner ℝ (H s) (H (t - s)) = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hr _
      (hseq ▸ Submodule.starProjection_apply_mem W (H t))
  have hnorm : inner ℝ (H (t - s)) (H (t - s)) = 0 := by
    calc
      _ = inner ℝ (H t) (H (t - s)) - inner ℝ (H s) (H (t - s)) := by
        conv_lhs => arg 2; rw [H.map_sub]
        exact inner_sub_left _ _ _
      _ = 0 := by rw [hzero, hszero, sub_self]
  have hequal : H t = H s := sub_eq_zero.mp (by
    rw [← H.map_sub]
    exact inner_self_eq_zero.mp hnorm)
  change V.starProjection (H f) ∈ W
  rw [← ht, hequal, hseq]
  exact Submodule.starProjection_apply_mem _ _


/-- The two genuine dual projections commute on actual unit-interval inputs,
for ultrafilters containing every tail. -/
theorem mixedDualHilbert_projections_commute_unit_interval
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    (mixedDualHilbertSubspace p R e U).starProjection
        ((mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f)) =
      (mixedDualHilbertSubspace p Q d U).starProjection
        ((mixedDualHilbertSubspace p R e U).starProjection (hilbertFamilyToCompletion _ U f)) := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  obtain ⟨t, htunit, ht⟩ := mixedDualHilbert_projection_exact_representative p R e U hU hs he f hf
  obtain ⟨u, huunit, hueq⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd f hf
  obtain ⟨v, hvunit, hveq⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd t htunit
  change H t = W.starProjection (H f) at ht
  change H u = V.starProjection (H f) at hueq
  change H v = V.starProjection (H t) at hveq
  have htm : H t ∈ W := ht ▸ Submodule.starProjection_apply_mem W (H f)
  have hvm : H v ∈ W := hveq ▸ mixedDualHilbert_projection_mem_other p Q d U hU hs hd R e he t htunit htm
  have hr : H (f - t) ∈ Wᗮ := by
    rw [H.map_sub, ht]
    exact W.sub_starProjection_mem_orthogonal _
  have huv : ∀ w c x, |(u - v).val w (c, x)| ≤ 1 := by
    intro w c x
    change |u.val w (c, x) - v.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(huunit w c x).1, (hvunit w c x).2],
      by linarith [(huunit w c x).2, (hvunit w c x).1]⟩
  have heq : H (u - v) = V.starProjection (H (f - t)) := by
    rw [H.map_sub, H.map_sub, map_sub, hueq, hveq]
  have hro : H (u - v) ∈ Wᗮ :=
    mixedDualHilbert_projected_orthogonal p Q d U hs hd R e he (f - t) (u - v) huv heq hr
  have hproj : W.starProjection (H u) = H v :=
    Submodule.eq_starProjection_of_mem_orthogonal hvm (by rwa [H.map_sub] at hro)
  change W.starProjection (V.starProjection (H f)) = V.starProjection (W.starProjection (H f))
  rw [← hueq, hproj, hveq, ht]

/-- A genuine unit-interval representative of the projection to the intersection,
characterized by membership and an orthogonal residual. -/
theorem mixedDualHilbert_intersection_unit_model
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t ∈
        mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U ∧
      hilbertFamilyToCompletion _ U (f - t) ∈
        (mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)ᗮ ∧
      hilbertFamilyToCompletion _ U t = (mixedDualHilbertSubspace p R e U).starProjection
        ((mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f)) := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  obtain ⟨u, huunit, hueq⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd f hf
  obtain ⟨t, htunit, hteq⟩ := mixedDualHilbert_projection_exact_representative p R e U hU hs he u huunit
  change H u = V.starProjection (H f) at hueq
  change H t = W.starProjection (H u) at hteq
  have hm : H t ∈ V ⊓ W := by
    constructor
    · have hcomm : W.starProjection (V.starProjection (H f)) = V.starProjection (W.starProjection (H f)) :=
        mixedDualHilbert_projections_commute_unit_interval p Q d U hU hs hd R e he f hf
      rw [hteq, hueq, hcomm]
      exact Submodule.starProjection_apply_mem _ _
    · rw [hteq]
      exact Submodule.starProjection_apply_mem _ _
  have ho : H (f - t) ∈ (V ⊓ W)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    rw [H.map_sub, inner_sub_left, hteq, hueq,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hz.2,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hz.1, sub_self]
  refine ⟨t, htunit, hm, ho, ?_⟩
  change H t = W.starProjection (V.starProjection (H f))
  rw [hteq, hueq]


/-- The second genuine projection preserves every vector of the first closed
space. The extension uses its bounded generators and continuity. -/
theorem mixedDualHilbert_projection_preserves_closed_space
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertSubspace p Q d U) :
    (mixedDualHilbertSubspace p R e U).starProjection z ∈ mixedDualHilbertSubspace p Q d U := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let T := V.comap W.starProjection.toLinearMap
  have hT : IsClosed (T : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)) :=
    (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).isClosed_topologicalClosure.preimage
      W.starProjection.continuous
  have hspan : Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) ≤ T := by
    apply Submodule.span_le.mpr
    intro z hzgen
    obtain ⟨f, hf, rfl⟩ := hzgen
    change W.starProjection (H f) ∈ V
    let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => (1 : ℝ)) 1 zero_le_one (by simp)
    have honeV : H one ∈ V := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (Q w) d, rfl⟩)
    have honeW : H one ∈ W := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (R w) e, rfl⟩)
    have hfm : H f ∈ V := (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨f, hf, rfl⟩)
    let plus := (1 / 2 : ℝ) • (f + one)
    have hpunit : ∀ w c x, 0 ≤ plus.val w (c, x) ∧ plus.val w (c, x) ≤ 1 := by
      intro w c x
      have hb := abs_le.mp (subgroupMixedDualHull_abs_le_one (Q w) d (hf w c) x)
      change 0 ≤ (1 / 2 : ℝ) * (f.val w (c, x) + 1) ∧
        (1 / 2 : ℝ) * (f.val w (c, x) + 1) ≤ 1
      constructor <;> linarith
    have hpm : H plus ∈ V := by
      change H ((1 / 2 : ℝ) • (f + one)) ∈ V
      rw [H.map_smul, H.map_add]
      exact V.smul_mem _ (V.add_mem hfm honeV)
    have hpW : W.starProjection (H plus) ∈ V :=
      mixedDualHilbert_projection_mem_other p R e U hU hs he Q d hd plus hpunit hpm
    have heq : f = (2 : ℝ) • plus - one := by
      apply Subtype.ext
      funext w x
      change f.val w x = 2 * ((1 / 2 : ℝ) * (f.val w x + 1)) - 1
      ring
    rw [heq, H.map_sub, H.map_smul, map_sub, map_smul,
      Submodule.starProjection_eq_self_iff.mpr honeW]
    exact V.sub_mem (V.smul_mem _ hpW) honeV
  exact (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).topologicalClosure_minimal hspan hT hz

/-- The actual dual projections commute on the entire completed Hilbert space. -/
theorem mixedDualHilbert_projections_commute
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :
    (mixedDualHilbertSubspace p R e U).starProjection
        ((mixedDualHilbertSubspace p Q d U).starProjection z) =
      (mixedDualHilbertSubspace p Q d U).starProjection
        ((mixedDualHilbertSubspace p R e U).starProjection z) := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  have hm : W.starProjection (V.starProjection z) ∈ V :=
    mixedDualHilbert_projection_preserves_closed_space p Q d U hU hs hd R e he
      (Submodule.starProjection_apply_mem _ _)
  have ho : W.starProjection z - W.starProjection (V.starProjection z) ∈ Vᗮ := by
    rw [← map_sub, Submodule.mem_orthogonal']
    intro v hv
    rw [Submodule.inner_starProjection_left_eq_right]
    exact (Submodule.mem_orthogonal' _ _).mp (V.sub_starProjection_mem_orthogonal z) _
      (mixedDualHilbert_projection_preserves_closed_space p Q d U hU hs hd R e he hv)
  exact (Submodule.eq_starProjection_of_mem_orthogonal hm ho).symm

end Hindman168
