import Hindman168.WeightedHaarHilbert

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

theorem finiteMassL2_unit_mul_norm_le {α : Type*} (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)]
    (u : α → ℝ) (hu : ∀ a, |u a| ≤ 1) (f : FiniteMassL2 μ) :
    @norm (FiniteMassL2 μ) _ (fun a => u a * f a) ≤ ‖f‖ := by
  have hsq : (@norm (FiniteMassL2 μ) _ (fun a => u a * f a)) ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [finiteMassL2_norm_sq, finiteMassL2_norm_sq]
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (hμ.out a)
    change (u a * f a) ^ 2 ≤ f a ^ 2
    have ha : (u a) ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg (u a)) zero_le_one).mpr (hu a)
      simpa only [sq_abs, one_pow] using h
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans_eq (one_mul _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

variable {G κ : ℕ → Type*} [∀ w, Fintype (G w)] [∀ w, Fintype (κ w)]
  (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]

/-- Actual coordinatewise multiplication by a unit-bounded family, on L2-bounded families. -/
noncomputable def weightedHaarMultiplier (u : ∀ w, κ w → G w → ℝ)
    (hu : ∀ w c x, |u w c x| ≤ 1) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) →ₗ[ℝ]
      boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) where
  toFun f := ⟨fun w z => u w z.1 z.2 * f.val w z, by
    obtain ⟨B, hB, hb⟩ := f.property
    exact ⟨B, hB, fun w => (finiteMassL2_unit_mul_norm_le _ (fun z => u w z.1 z.2)
      (fun z => hu w z.1 z.2) (f.val w)).trans (hb w)⟩⟩
  map_add' f g := by
    apply Subtype.ext
    funext w
    funext z
    change u w z.1 z.2 * (f.val w z + g.val w z) = _
    exact mul_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    funext w
    funext z
    change u w z.1 z.2 * (r * f.val w z) = r * (u w z.1 z.2 * f.val w z)
    ring

theorem weightedHaarMultiplier_hilbert_distance_le (U : Ultrafilter ℕ)
    (u : ∀ w, κ w → G w → ℝ) (hu : ∀ w c x, |u w c x| ≤ 1)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    ‖hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) -
      hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu g)‖ ≤
      ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U g‖ := by
  have hb (w : ℕ) : ‖(weightedHaarMultiplier p u hu f).val w -
      (weightedHaarMultiplier p u hu g).val w‖ ≤ ‖f.val w - g.val w‖ := by
    have he : (weightedHaarMultiplier p u hu f).val w - (weightedHaarMultiplier p u hu g).val w =
        (fun z => u w z.1 z.2 * (f.val w z - g.val w z)) := by funext z; exact (mul_sub _ _ _).symm
    rw [he]
    exact finiteMassL2_unit_mul_norm_le (weightedHaarMass (G := G w) (p w))
      (fun z => u w z.1 z.2) (fun z => hu w z.1 z.2) (f.val w - g.val w)
  have hs := le_of_tendsto_of_tendsto
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U (weightedHaarMultiplier p u hu f) (weightedHaarMultiplier p u hu g))
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f g)
    (Eventually.of_forall (fun w => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb w)))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem weightedHaarMultiplier_hilbert_inner (U : Ultrafilter ℕ)
    (u : ∀ w, κ w → G w → ℝ) (hu : ∀ w c x, |u w c x| ≤ 1)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    inner ℝ (hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f)) (hilbertFamilyToCompletion _ U g) =
      inner ℝ (hilbertFamilyToCompletion _ U f) (hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu g)) := by
  rw [hilbertFamilyToCompletion_inner, hilbertFamilyToCompletion_inner]
  unfold hilbertFamilyPairing
  congr 1
  funext w
  change expectation (weightedHaarMass (G := G w) (p w)) (fun z => (u w z.1 z.2 * f.val w z) * g.val w z) =
    expectation _ (fun z => f.val w z * (u w z.1 z.2 * g.val w z))
  congr 1
  funext z
  ring

end Hindman168
