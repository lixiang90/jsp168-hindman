import Hindman168.MixedDualInternalLocalization
import Hindman168.WeightedHaarUniformSelection

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- The lower-order coefficient in the actual mixed-dual recursion retains
both the lower first-direction structure and the second-direction structure.
The two shifts may vary with the stage and cell. -/
theorem mixedDualHilbert_recursive_inputs_localized
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U)
    (a b : ∀ w, κ w → G w) :
    ∃ t : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ ω, ω ≠ ∅ → ∀ w c x, |(t ω).val w (c, x)| ≤ 1) ∧
      (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (t ω) ∈ mixedDualHilbertSubspace p R e U) ∧
      ∀ ω w c x, (t ω).val w (c, x) =
        (f (ω.image Fin.succ)).val w (c, x + a w c) *
          (f (insert 0 (ω.image Fin.succ))).val w (c, x + b w c) := by
  let v := fun ω : Finset (Fin d) => weightedHaarTranslation p a (f (ω.image Fin.succ))
  let u := fun ω : Finset (Fin d) => weightedHaarTranslation p b (f (insert 0 (ω.image Fin.succ)))
  have hub : ∀ ω : Finset (Fin d), ∀ w c x, |(u ω).val w (c, x)| ≤ 1 := by
    intro ω w c x
    exact hu (insert 0 (ω.image Fin.succ)) (by simp) w c _
  let t := fun ω : Finset (Fin d) => weightedHaarMultiplier p
    (fun w c x => (u ω).val w (c, x)) (hub ω) (v ω)
  have hunit : ∀ ω : Finset (Fin d), ω ≠ ∅ → ∀ w c x, |(t ω).val w (c, x)| ≤ 1 := by
    intro ω hω w c x
    have him : ω.image Fin.succ ≠ ∅ := fun h => hω (Finset.image_eq_empty.mp h)
    change |(u ω).val w (c, x) * (v ω).val w (c, x)| ≤ 1
    rw [abs_mul]
    exact (mul_le_mul (hub ω w c x) (hu (ω.image Fin.succ) him w c _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hstruct : ∀ ω : Finset (Fin d), ω ≠ ∅ → hilbertFamilyToCompletion _ U (t ω) ∈
      mixedDualHilbertSubspace p R e U := by
    intro ω hω
    have him : ω.image Fin.succ ≠ ∅ := fun h => hω (Finset.image_eq_empty.mp h)
    exact mixedDualHilbert_structured_product_closed p R e U hs he (u ω) (hub ω)
      (mixedDualHilbert_translation_closed p R e U hs he b _ (hf _ (by simp))) (v ω)
      (mixedDualHilbert_translation_closed p R e U hs he a _ (hf _ him))
  refine ⟨t, hunit, hstruct, ?_⟩
  intro ω w c x
  change (f (insert 0 (ω.image Fin.succ))).val w (c, x + b w c) *
    (f (ω.image Fin.succ)).val w (c, x + a w c) = _
  exact mul_comm _ _

theorem mixedDualHilbert_actual_mixed_dual_representative
    (hs : ∀ w, ∑ c, p w c = 1)
    (f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1) :
    ∃ C : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |C.val w (c, x)| ≤ 1) ∧
      hilbertFamilyToCompletion _ U C ∈ mixedDualHilbertGenerators p Q d U ∧
      ∀ w c x, C.val w (c, x) = subgroupMixedDualFunction (Q w) d (fun ω y => (f ω).val w (c, y)) x := by
  let F : ∀ w, κ w → G w → ℝ := fun w c x =>
    subgroupMixedDualFunction (Q w) d (fun ω y => (f ω).val w (c, y)) x
  have hF : ∀ w c x, |F w c x| ≤ 1 := fun w c x =>
    subgroupMixedDualFunction_abs_le_one (Q w) d (fun ω y => (f ω).val w (c, y)) (fun ω hω y => hu ω hω w c y) x
  let C := weightedHaarBoundedFamily p hs F 1 zero_le_one hF
  have hgen : hilbertFamilyToCompletion _ U C ∈ mixedDualHilbertGenerators p Q d U := by
    refine ⟨C, ?_, rfl⟩
    intro w c
    change subgroupMixedDualFunction (Q w) d (fun ω y => (f ω).val w (c, y)) ∈ subgroupMixedDualHull (Q w) d
    exact subgroupMixedDualFunction_mem_hull (Q w) d (fun ω y => (f ω).val w (c, y))
      (fun ω hω y => hu ω hω w c y)
  exact ⟨C, hF, hgen, fun _ _ _ => rfl⟩

theorem mixedDualHilbert_recursive_coefficient_localized
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U)
    (a b : ∀ w, κ w → G w) :
    ∃ C : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |C.val w (c, x)| ≤ 1) ∧
      hilbertFamilyToCompletion _ U C ∈
        mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U ∧
      ∀ w c x, C.val w (c, x) = subgroupMixedDualFunction (Q w) d (fun ω y =>
        (f (ω.image Fin.succ)).val w (c, y + a w c) *
          (f (insert 0 (ω.image Fin.succ))).val w (c, y + b w c)) x := by
  obtain ⟨t, hunit, hstruct, htval⟩ := mixedDualHilbert_recursive_inputs_localized p d U hs R e he f hu hf a b
  obtain ⟨C, hC, hgen, hCval⟩ := mixedDualHilbert_actual_mixed_dual_representative p Q d U hs t hunit
  have hR : hilbertFamilyToCompletion _ U C ∈ mixedDualHilbertSubspace p R e U :=
    mixedDualHilbert_internal_dual_closed p R e U hs he Q d t hunit hstruct C hCval
  refine ⟨C, hC, ⟨(Submodule.le_topologicalClosure _) (Submodule.subset_span hgen), hR⟩, ?_⟩
  intro w c x
  rw [hCval]
  congr 1
  funext ω y
  exact htval ω w c y


/-- Orthogonality to the lower intersection controls all recursive coefficients
uniformly, including shifts selected separately at every stage and cell. -/
theorem mixedDualHilbert_recursive_coefficients_uniform_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : hilbertFamilyToCompletion _ U g ∈
      (mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)ᗮ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in (U : Filter ℕ), ∀ a b : κ w → G w,
      |∑ c, p w c * finiteHaarMean (fun x => g.val w (c, x) *
        subgroupMixedDualFunction (Q w) d (fun ω y =>
          (f (ω.image Fin.succ)).val w (c, y + a c) *
            (f (insert 0 (ω.image Fin.succ))).val w (c, y + b c)) x)| < ε := by
  let A := fun w => (κ w → G w) × (κ w → G w)
  let F := fun w (a : A w) (c : κ w) (x : G w) =>
    subgroupMixedDualFunction (Q w) d (fun ω y =>
      (f (ω.image Fin.succ)).val w (c, y + a.1 c) *
        (f (insert 0 (ω.image Fin.succ))).val w (c, y + a.2 c)) x
  have hF : ∀ w a c x, |F w a c x| ≤ 1 := by
    intro w a c x
    apply subgroupMixedDualFunction_abs_le_one (Q w) d
    intro ω hω y
    have him : ω.image Fin.succ ≠ ∅ := fun h => hω (Finset.image_eq_empty.mp h)
    rw [abs_mul]
    exact (mul_le_mul (hu (ω.image Fin.succ) him w c _)
      (hu (insert 0 (ω.image Fin.succ)) (by simp) w c _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hselected : ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
    intro a
    obtain ⟨C, _, hC, hval⟩ := mixedDualHilbert_recursive_coefficient_localized p Q d U hs R e he f hu hf
      (fun w c => (a w).1 c) (fun w c => (a w).2 c)
    have heq : C = weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x) := by
      apply Subtype.ext
      funext w z
      exact hval w z.1 z.2
    rwa [← heq]
  have huniform := weightedHaarHilbert_uniform_orthogonal p hs U
    (mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U) F hF hselected g hg
  intro ε hε
  filter_upwards [huniform ε hε] with w hw
  intro a b
  exact hw (a, b)

end Hindman168
