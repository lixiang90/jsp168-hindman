import Hindman168.WeightedHaarHilbert

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- Testing every dependent stage-varying selection gives one uniform bound.
No bounded cardinality of the parameter types is required. -/
theorem uniform_abs_small_of_all_dependent_selections {ι : Type*}
    (L : Filter ι) (A : ι → Type*) [∀ i, Nonempty (A i)]
    (r : ∀ i, A i → ℝ)
    (hr : ∀ a : ∀ i, A i, Tendsto (fun i => r i (a i)) L (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in L, ∀ a, |r i a| < ε := by
  intro ε hε
  have hc (i : ι) : ∃ a : A i, ((∃ b : A i, ε ≤ |r i b|) → ε ≤ |r i a|) := by
    by_cases h : ∃ b : A i, ε ≤ |r i b|
    · obtain ⟨a, ha⟩ := h
      exact ⟨a, fun _ => ha⟩
    · exact ⟨Classical.choice (inferInstance : Nonempty (A i)), fun hb => False.elim (h hb)⟩
  choose a ha using hc
  have ht := (hr a).abs.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hε))
  filter_upwards [ht] with i hi
  intro b
  by_contra hb
  exact (not_le_of_gt (by simpa only [abs_zero] using hi)) (ha i ⟨b, le_of_not_gt hb⟩)

theorem weightedHaarHilbert_uniform_orthogonal
    {G κ A : ℕ → Type*} [∀ w, Fintype (G w)] [∀ w, Nonempty (G w)]
    [∀ w, Fintype (κ w)] [∀ w, Nonempty (A w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ)
    (V : Submodule ℝ (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
    (F : ∀ w, A w → κ w → G w → ℝ) (hF : ∀ w a c x, |F w a c x| ≤ 1)
    (hselected : ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)) ∈ V)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : hilbertFamilyToCompletion _ U g ∈ Vᗮ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in (U : Filter ℕ), ∀ a : A w,
      |∑ c, p w c * finiteHaarMean (fun x => g.val w (c, x) * F w a c x)| < ε := by
  apply uniform_abs_small_of_all_dependent_selections
  intro a
  let f := weightedHaarBoundedFamily p hs (fun w c x => F w (a w) c x) 1 zero_le_one
    (fun w c x => hF w (a w) c x)
  have hz := (Submodule.mem_orthogonal' _ _).mp hg _ (hselected a)
  have ht := weightedHaarHilbert_inner_tendsto p U g f
  rw [hz] at ht
  exact ht

end Hindman168
