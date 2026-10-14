import Hindman168.WeightedHaarHilbert

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

theorem weightedHaarL2_translate_norm {G κ : Type*} [AddCommGroup G] [Fintype G]
    [Fintype κ] (p : κ → ℝ) [Fact (∀ c, 0 ≤ p c)] (a : κ → G)
    (f : FiniteMassL2 (weightedHaarMass (G := G) p)) :
    @norm (FiniteMassL2 (weightedHaarMass (G := G) p)) _ (fun z => f (z.1, z.2 + a z.1)) = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [finiteMassL2_norm_sq, finiteMassL2_norm_sq, weightedHaarMass_expectation, weightedHaarMass_expectation]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact (by simpa only [add_comm] using finiteHaarMean_add_left (fun x => (f (c, x)) ^ 2) (a c))

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]

/-- Cellwise translation of actual L2-bounded families. Shifts may depend on the stage and cell. -/
noncomputable def weightedHaarTranslation (a : ∀ w, κ w → G w) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) →ₗ[ℝ]
      boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) where
  toFun f := ⟨fun w z => f.val w (z.1, z.2 + a w z.1), by
    obtain ⟨B, hB, hb⟩ := f.property
    exact ⟨B, hB, fun w => (weightedHaarL2_translate_norm (p w) (a w) (f.val w)).le.trans (hb w)⟩⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

theorem weightedHaarTranslation_hilbert_distance (U : Ultrafilter ℕ)
    (a : ∀ w, κ w → G w)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    ‖hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f) -
      hilbertFamilyToCompletion _ U (weightedHaarTranslation p a g)‖ =
      ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply tendsto_nhds_unique (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U
    (weightedHaarTranslation p a f) (weightedHaarTranslation p a g))
  have he (w : ℕ) : ‖(weightedHaarTranslation p a f).val w -
      (weightedHaarTranslation p a g).val w‖ = ‖f.val w - g.val w‖ :=
    weightedHaarL2_translate_norm (p w) (a w) (f.val w - g.val w)
  simpa only [he] using hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f g

theorem weightedHaarTranslation_hilbert_inner (U : Ultrafilter ℕ)
    (a : ∀ w, κ w → G w)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    inner ℝ (hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f)) (hilbertFamilyToCompletion _ U g) =
      inner ℝ (hilbertFamilyToCompletion _ U f)
        (hilbertFamilyToCompletion _ U (weightedHaarTranslation p (fun w c => -a w c) g)) := by
  rw [hilbertFamilyToCompletion_inner, hilbertFamilyToCompletion_inner]
  unfold hilbertFamilyPairing
  congr 1
  funext w
  change expectation (weightedHaarMass (G := G w) (p w))
      (fun z => f.val w (z.1, z.2 + a w z.1) * g.val w z) =
    expectation _ (fun z => f.val w z * g.val w (z.1, z.2 + -a w z.1))
  rw [weightedHaarMass_expectation, weightedHaarMass_expectation]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simpa only [add_comm (a w c), add_neg_cancel_right] using
    finiteHaarMean_add_left (fun x => f.val w (c, x) * g.val w (c, x + -a w c)) (a w c)

end Hindman168
