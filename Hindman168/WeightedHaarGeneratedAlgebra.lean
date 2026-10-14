import Hindman168.WeightedHaarMultiplication
import Hindman168.MixedDualHilbertRepresentatives

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ)
  (A : Set (boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))))
  (hA : ∀ f ∈ A, ∀ w c x, |f.val w (c, x)| ≤ 1)

include hA

/-- An algebraic span of actual unit generators has actual representatives
with a uniform pointwise bound. The bound may depend on the span vector. -/
theorem weightedHaarHilbert_unit_span_representative
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)) :
    ∃ f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      f ∈ Submodule.span ℝ A ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ w c x, |f.val w (c, x)| ≤ B) ∧ hilbertFamilyToCompletion _ U f = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    exact ⟨f, Submodule.subset_span hf, 1, zero_le_one, hA f hf, rfl⟩
  | zero =>
    refine ⟨0, Submodule.zero_mem _, 0, le_rfl, ?_, (hilbertFamilyCompletionLinearMap _ U).map_zero⟩
    intro w c x
    change |(0 : ℝ)| ≤ 0
    simp only [abs_zero, le_refl]
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, B, hB, hb, he⟩ := hx
    obtain ⟨g, hg, C, hC, hc, he'⟩ := hy
    refine ⟨f + g, Submodule.add_mem _ hf hg, B + C, add_nonneg hB hC, ?_, ?_⟩
    · intro w c x
      change |f.val w (c, x) + g.val w (c, x)| ≤ B + C
      exact (abs_add_le _ _).trans (add_le_add (hb w c x) (hc w c x))
    · exact ((hilbertFamilyCompletionLinearMap _ U).map_add f g).trans (congrArg₂ (· + ·) he he')
  | smul r x _ hx =>
    obtain ⟨f, hf, B, hB, hb, he⟩ := hx
    refine ⟨r • f, Submodule.smul_mem _ r hf, |r| * B, mul_nonneg (abs_nonneg _) hB, ?_, ?_⟩
    · intro w c x
      change |r * f.val w (c, x)| ≤ |r| * B
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb w c x) (abs_nonneg _)
    · exact ((hilbertFamilyCompletionLinearMap _ U).map_smul r f).trans (congrArg (r • ·) he)

theorem weightedHaarHilbert_generated_closed_approximation
    (V : Submodule ℝ (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
    (hV : V = (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).topologicalClosure)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      f ∈ Submodule.span ℝ A ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ w c x, |f.val w (c, x)| ≤ B) ∧ hilbertFamilyToCompletion _ U f ∈ V ∧
      ‖z - hilbertFamilyToCompletion _ U f‖ < ε := by
  rw [hV] at hz
  obtain ⟨t, ht, he⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨f, hf, B, hB, hb, hrep⟩ := weightedHaarHilbert_unit_span_representative p U A hA ht
  refine ⟨f, hf, B, hB, hb, ?_, ?_⟩
  · rw [hV, hrep]
    exact Submodule.le_topologicalClosure _ ht
  · rw [hrep]
    simpa only [dist_eq_norm] using he

theorem weightedHaarHilbert_generated_multiplier_closed
    (V : Submodule ℝ (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
    (hV : V = (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).topologicalClosure)
    (u : ∀ w, κ w → G w → ℝ) (hu : ∀ w c x, |u w c x| ≤ 1)
    (hgen : ∀ a ∈ A, hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu a) ∈ V)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ V) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) ∈ V := by
  have hs : Submodule.span ℝ A ≤ V.comap
      ((hilbertFamilyCompletionLinearMap _ U).comp (weightedHaarMultiplier p u hu)) :=
    Submodule.span_le.mpr hgen
  have hc : IsClosed (V : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)) := by
    rw [hV]
    exact (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).isClosed_topologicalClosure
  apply hc.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨t, ht, _, _, _, _, he⟩ := weightedHaarHilbert_generated_closed_approximation p U A hA V hV hf hε
  refine ⟨hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu t), hs ht, ?_⟩
  rw [dist_eq_norm]
  exact (weightedHaarMultiplier_hilbert_distance_le p U u hu f t).trans_lt he

/-- Closure of products of actual unit generators extends to products with
every actual unit represented member of their closed Hilbert span. -/
theorem weightedHaarHilbert_generated_unit_product_closed
    (V : Submodule ℝ (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
    (hV : V = (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).topologicalClosure)
    (hpair : ∀ a, ∀ ha : a ∈ A, ∀ b ∈ A, hilbertFamilyToCompletion _ U
      (weightedHaarMultiplier p (fun w c x => a.val w (c, x)) (hA a ha) b) ∈ V)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1) (hustruct : hilbertFamilyToCompletion _ U u ∈ V)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ V) :
    hilbertFamilyToCompletion _ U
      (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f) ∈ V := by
  have hgen : ∀ b ∈ A, hilbertFamilyToCompletion _ U
      (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu b) ∈ V := by
    intro b hb
    have hm := weightedHaarHilbert_generated_multiplier_closed p U A hA V hV
      (fun w c x => b.val w (c, x)) (hA b hb) (fun a ha => hpair b hb a ha) u hustruct
    have he : weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu b =
        weightedHaarMultiplier p (fun w c x => b.val w (c, x)) (hA b hb) u := by
      apply Subtype.ext
      funext w z
      change u.val w z * b.val w z = b.val w z * u.val w z
      exact mul_comm _ _
    rwa [he]
  exact weightedHaarHilbert_generated_multiplier_closed p U A hA V hV
    (fun w c x => u.val w (c, x)) hu hgen f hf

end Hindman168
