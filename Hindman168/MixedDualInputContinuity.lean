import Hindman168.MixedDualRecursion
import Hindman168.WeightedHaarHilbert
import Hindman168.FiniteHaarCauchySchwarz

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- Isolate one nonroot input of the actual mixed dual. -/
theorem subgroupMixedDualFunction_input_average {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d)) (hS : S ≠ ∅)
    (F : Finset (Fin d) → G → ℝ) (u : G → ℝ) (x : G) :
    subgroupMixedDualFunction Q d (fun ω y => if ω = S then u y else F ω y) x =
      finiteHaarMean (fun v : Fin d → Q => u (x + ∑ j ∈ S, (v j : G)) *
        ∏ ω ∈ ((Finset.univ : Finset (Finset (Fin d))).erase ∅).erase S,
          F ω (x + ∑ j ∈ ω, (v j : G))) := by
  unfold subgroupMixedDualFunction
  congr 1
  funext v
  rw [← Finset.mul_prod_erase _ _ (show S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅ by simp [hS])]
  congr 1
  · exact if_pos rfl
  · apply Finset.prod_congr rfl
    intro ω hω
    dsimp only
    rw [if_neg (Finset.mem_erase.mp hω).1]

/-- With the other inputs unit bounded, replacing a single nonroot input
defines a contraction for the original weighted finite Haar L2 norm. -/
theorem weightedMixedDualInput_norm_le {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (Q : AddSubgroup G) [Fintype Q]
    (p : κ → ℝ) [Fact (∀ c, 0 ≤ p c)] (d : ℕ) (S : Finset (Fin d)) (hS : S ≠ ∅)
    (F : κ → Finset (Fin d) → G → ℝ)
    (hF : ∀ c ω, ω ≠ ∅ → ω ≠ S → ∀ x, |F c ω x| ≤ 1)
    (u : FiniteMassL2 (weightedHaarMass (G := G) p)) :
    @norm (FiniteMassL2 (weightedHaarMass (G := G) p)) _
      (fun z => subgroupMixedDualFunction Q d
        (fun ω y => if ω = S then u (z.1, y) else F z.1 ω y) z.2) ≤ ‖u‖ := by
  let K := fun (c : κ) (x : G) (v : Fin d → Q) =>
    ∏ ω ∈ ((Finset.univ : Finset (Finset (Fin d))).erase ∅).erase S,
      F c ω (x + ∑ j ∈ ω, (v j : G))
  have hK : ∀ c x v, |K c x v| ≤ 1 := by
    intro c x v
    dsimp only [K]
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro ω hω
    exact hF c ω (Finset.mem_erase.mp (Finset.mem_erase.mp hω).2).1 (Finset.mem_erase.mp hω).1 _
  have hc (c : κ) : finiteHaarMean (fun x =>
      subgroupMixedDualFunction Q d (fun ω y => if ω = S then u (c, y) else F c ω y) x ^ 2) ≤
        finiteHaarMean (fun x => u (c, x) ^ 2) := by
    calc
      _ ≤ finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q =>
          u (c, x + ∑ j ∈ S, (v j : G)) ^ 2)) := by
        apply finiteHaarMean_mono
        intro x
        rw [subgroupMixedDualFunction_input_average Q d S hS]
        simpa only [mul_comm] using finiteHaarMean_discard_unit_factor (K c x)
          (fun v : Fin d → Q => u (c, x + ∑ j ∈ S, (v j : G))) (hK c x)
      _ = finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
          u (c, x + ∑ j ∈ S, (v j : G)) ^ 2)) := finiteHaarMean_comm _
      _ = _ := by
        have ht (v : Fin d → Q) : finiteHaarMean (fun x => u (c, x + ∑ j ∈ S, (v j : G)) ^ 2) =
            finiteHaarMean (fun x => u (c, x) ^ 2) :=
          finiteHaarMean_equiv (Equiv.addRight (∑ j ∈ S, (v j : G))) (fun x => u (c, x) ^ 2)
        simp only [ht, finiteHaarMean_const]
  have hs : (@norm (FiniteMassL2 (weightedHaarMass (G := G) p)) _
      (fun z => subgroupMixedDualFunction Q d
        (fun ω y => if ω = S then u (z.1, y) else F z.1 ω y) z.2)) ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [finiteMassL2_norm_sq, finiteMassL2_norm_sq, weightedHaarMass_expectation, weightedHaarMass_expectation]
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_left (hc c) ((Fact.out : ∀ c, 0 ≤ p c) c)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ)
  (S : Finset (Fin d)) (hS : S ≠ ∅)
  (F : ∀ w, κ w → Finset (Fin d) → G w → ℝ)
  (hF : ∀ w c ω, ω ≠ ∅ → ω ≠ S → ∀ x, |F w c ω x| ≤ 1)

/-- The actual first-direction dual as a linear map of one nonroot input,
on L2-bounded families. No pointwise bound on that input is required. -/
noncomputable def weightedMixedDualInput :
    boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) →ₗ[ℝ]
      boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) where
  toFun u := ⟨fun w z => subgroupMixedDualFunction (Q w) d
      (fun ω y => if ω = S then u.val w (z.1, y) else F w z.1 ω y) z.2, by
    obtain ⟨B, hB, hb⟩ := u.property
    exact ⟨B, hB, fun w => (weightedMixedDualInput_norm_le (Q w) (p w) d S hS (F w) (hF w) (u.val w)).trans (hb w)⟩⟩
  map_add' u v := by
    apply Subtype.ext
    funext w z
    change subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then
        u.val w (z.1, y) + v.val w (z.1, y) else F w z.1 ω y) z.2 =
      subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then u.val w (z.1, y) else F w z.1 ω y) z.2 +
        subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then v.val w (z.1, y) else F w z.1 ω y) z.2
    simp only [subgroupMixedDualFunction_input_average (Q w) d S hS, add_mul, finiteHaarMean_add]
  map_smul' r u := by
    apply Subtype.ext
    funext w z
    change subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then
        r * u.val w (z.1, y) else F w z.1 ω y) z.2 =
      r * subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then u.val w (z.1, y) else F w z.1 ω y) z.2
    simp only [subgroupMixedDualFunction_input_average (Q w) d S hS, mul_assoc, finiteHaarMean_const_mul]

theorem weightedMixedDualInput_apply
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) (w : ℕ) (c : κ w) (x : G w) :
    (weightedMixedDualInput p Q d S hS F hF u).val w (c, x) =
      subgroupMixedDualFunction (Q w) d (fun ω y => if ω = S then u.val w (c, y) else F w c ω y) x := rfl

theorem weightedMixedDualInput_hilbert_distance_le (U : Ultrafilter ℕ)
    (u v : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    ‖hilbertFamilyToCompletion _ U (weightedMixedDualInput p Q d S hS F hF u) -
        hilbertFamilyToCompletion _ U (weightedMixedDualInput p Q d S hS F hF v)‖ ≤
      ‖hilbertFamilyToCompletion _ U u - hilbertFamilyToCompletion _ U v‖ := by
  let L := weightedMixedDualInput p Q d S hS F hF
  have hb (w : ℕ) : ‖(L u).val w - (L v).val w‖ ≤ ‖u.val w - v.val w‖ := by
    have he : (L u).val w - (L v).val w = (L (u - v)).val w :=
      (congrArg (fun f => f.val w) (L.map_sub u v)).symm
    rw [he]
    exact weightedMixedDualInput_norm_le (Q w) (p w) d S hS (F w) (hF w) ((u - v).val w)
  have hs := le_of_tendsto_of_tendsto
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U (L u) (L v))
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U u v)
    (Eventually.of_forall (fun w => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb w)))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end Hindman168
