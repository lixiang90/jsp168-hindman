import Hindman168.MixedDualHilbertOrthogonality
import Hindman168.MixedDualBalancedHull

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

theorem mixedDualHilbertGenerators_convex : Convex ℝ (mixedDualHilbertGenerators p Q d U) := by
  rintro z ⟨f, hf, rfl⟩ t ⟨g, hg, rfl⟩ a b ha hb hab
  refine ⟨a • f + b • g, ?_, ?_⟩
  · intro w c
    exact (convex_convexHull ℝ _) (hf w c) (hg w c) ha hb hab
  · exact (hilbertFamilyCompletionLinearMap _ U).map_add (a • f) (b • g) |>.trans
      (congrArg₂ (· + ·) ((hilbertFamilyCompletionLinearMap _ U).map_smul a f)
        ((hilbertFamilyCompletionLinearMap _ U).map_smul b g))

theorem mixedDualHilbertGenerators_neg (hd : 0 < d)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertGenerators p Q d U) : -z ∈ mixedDualHilbertGenerators p Q d U := by
  obtain ⟨f, hf, rfl⟩ := hz
  exact ⟨-f, fun w c => subgroupMixedDualHull_neg_mem (Q w) d hd (hf w c),
    (hilbertFamilyCompletionLinearMap _ U).map_neg f⟩

theorem mixedDualHilbertGenerators_zero (hd : 0 < d) :
    (0 : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)
      ∈ mixedDualHilbertGenerators p Q d U := by
  exact ⟨0, fun w _ => subgroupMixedDualHull_zero_mem (Q w) d hd,
    (hilbertFamilyCompletionLinearMap _ U).map_zero⟩

/-- Every vector in the algebraic span has a representative with one uniform bound
and the same nonnegative scalar multiplying a dual-hull member in every cell. -/
theorem mixedDualHilbert_span_representative (hd : 0 < d)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ f : boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |f.val w (c, x)| ≤ B) ∧
      (∀ w c, ∃ u ∈ subgroupMixedDualHull (Q w) d, (fun x => f.val w (c, x)) = B • u) ∧
      hilbertFamilyToCompletion _ U f = z := by
  obtain ⟨B, hB, u, ⟨f, hf, rfl⟩, rfl⟩ := convex_symmetric_span_representation _
    (mixedDualHilbertGenerators_convex p Q d U) (mixedDualHilbertGenerators_zero p Q d U hd)
    (fun _ hz => mixedDualHilbertGenerators_neg p Q d U hd hz) hz
  refine ⟨B, hB, B • f, ?_, ?_, (hilbertFamilyCompletionLinearMap _ U).map_smul B f⟩
  · intro w c x
    change |B * f.val w (c, x)| ≤ B
    rw [abs_mul, abs_of_nonneg hB]
    exact (mul_le_mul_of_nonneg_left (subgroupMixedDualHull_abs_le_one (Q w) d (hf w c) x) hB).trans_eq (mul_one B)
  · intro w c
    exact ⟨fun x => f.val w (c, x), hf w c, rfl⟩

theorem mixedDualHilbert_closed_approximation (hd : 0 < d)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertSubspace p Q d U) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ f : boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |f.val w (c, x)| ≤ B) ∧
      (∀ w c, ∃ u ∈ subgroupMixedDualHull (Q w) d, (fun x => f.val w (c, x)) = B • u) ∧
      hilbertFamilyToCompletion _ U f ∈ Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) ∧
      ‖z - hilbertFamilyToCompletion _ U f‖ < ε := by
  obtain ⟨t, ht, he⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨B, hB, f, hf, hr, rfl⟩ := mixedDualHilbert_span_representative p Q d U hd ht
  exact ⟨B, hB, f, hf, hr, ht, by simpa only [dist_eq_norm] using he⟩

end Hindman168
