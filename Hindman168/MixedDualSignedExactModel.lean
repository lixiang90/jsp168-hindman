import Hindman168.MixedDualExactModel

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- Affine normalization extends the exact unit-interval projection model
to every actual real unit-bounded input, retaining a unit-bounded model. -/
theorem mixedDualHilbert_projection_signed_exact_representative
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, |f.val w (c, x)| ≤ 1) :
    ∃ q : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |q.val w (c, x)| ≤ 1) ∧
      hilbertFamilyToCompletion _ U q =
        (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) := by
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let V := mixedDualHilbertSubspace p Q d U
  let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => (1 : ℝ))
    1 zero_le_one (by simp)
  have hone : H one ∈ V := (Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (Q w) d, rfl⟩)
  let plus := (1 / 2 : ℝ) • (f + one)
  have hpunit : ∀ w c x, 0 ≤ plus.val w (c, x) ∧ plus.val w (c, x) ≤ 1 := by
    intro w c x
    have hb := abs_le.mp (hf w c x)
    change 0 ≤ (1 / 2 : ℝ) * (f.val w (c, x) + 1) ∧
      (1 / 2 : ℝ) * (f.val w (c, x) + 1) ≤ 1
    constructor <;> linarith
  obtain ⟨t, htunit, ht⟩ := mixedDualHilbert_projection_exact_representative
    p Q d U hU hs hd plus hpunit
  change H t = V.starProjection (H plus) at ht
  let q := (2 : ℝ) • t - one
  refine ⟨q, ?_, ?_⟩
  · intro w c x
    change |2 * t.val w (c, x) - 1| ≤ 1
    exact abs_le.mpr ⟨by linarith [(htunit w c x).1], by linarith [(htunit w c x).2]⟩
  · have hfrep : f = (2 : ℝ) • plus - one := by
      apply Subtype.ext
      funext w z
      change f.val w z = 2 * ((1 / 2 : ℝ) * (f.val w z + 1)) - 1
      ring
    have hfv : H f = (2 : ℝ) • H plus - H one := by
      rw [hfrep, H.map_sub, H.map_smul]
    change H ((2 : ℝ) • t - one) = V.starProjection (H f)
    rw [H.map_sub, H.map_smul, ht, hfv, V.starProjection.map_sub, V.starProjection.map_smul,
      Submodule.starProjection_eq_self_iff.mpr hone]

end Hindman168
