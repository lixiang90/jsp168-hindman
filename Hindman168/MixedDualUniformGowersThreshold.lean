import Hindman168.UltrafilterUniformThreshold
import Hindman168.MixedDualRecursiveLocalization

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- A positive threshold tests every parameter and every actual unit function
against a varying family of structured functions, eventually along the same ultrafilter. -/
theorem mixedDualHilbert_uniform_gowers_threshold
    {G κ A : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)] [∀ w, Nonempty (A w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (S w)] (k : ℕ) (hk : 0 < k)
    (F : ∀ w, A w → κ w → G w → ℝ) (hF : ∀ w a c x, |F w a c x| ≤ 1)
    (hselected : ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)) ∈
      mixedDualHilbertSubspace p S k U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in (U : Filter ℕ),
      ∀ (a : A w) (g : κ w → G w → ℝ), (∀ c x, |g c x| ≤ 1) →
        weightedSubgroupGowersValue (S w) (p w) k g ≤ δ →
          |∑ c, p w c * finiteHaarMean (fun x => g c x * F w a c x)| < ε := by
  let B := fun w => {g : κ w → G w → ℝ // ∀ c x, |g c x| ≤ 1}
  letI (w : ℕ) : Nonempty (B w) := ⟨⟨fun _ _ => 0, by simp⟩⟩
  let N := fun w (g : B w) => weightedSubgroupGowersValue (S w) (p w) k g.val
  let r := fun w (a : A w) (g : B w) =>
    ∑ c, p w c * finiteHaarMean (fun x => g.val c x * F w a c x)
  have hN : ∀ w g, 0 ≤ N w g := fun w g =>
    weightedSubgroupGowersValue_nonneg (S w) (p w) Fact.out k hk g.val
  have hnull : ∀ (a : ∀ w, A w) (b : ∀ w, B w),
      Tendsto (fun w => N w (b w)) (U : Filter ℕ) (𝓝 0) →
        Tendsto (fun w => r w (a w) (b w)) (U : Filter ℕ) (𝓝 0) := by
    intro a b hzero
    let g := weightedHaarBoundedFamily p hs (fun w c x => (b w).val c x)
      1 zero_le_one (fun w c x => (b w).property c x)
    let f := weightedHaarBoundedFamily p hs (fun w c x => F w (a w) c x)
      1 zero_le_one (fun w c x => hF w (a w) c x)
    have ho : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p S k U)ᗮ :=
      mixedDualHilbert_orthogonal_of_gowers_zero p S k U hs hk g hzero
    have hz := (Submodule.mem_orthogonal' _ _).mp ho _ (hselected a)
    have ht := weightedHaarHilbert_inner_tendsto p U g f
    rw [hz] at ht
    exact ht
  intro ε hε
  obtain ⟨δ, hδ, he⟩ := ultrafilter_uniform_null_test_threshold U hU A B N hN r hnull ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [he] with w hw
  intro a g hg
  exact hw a ⟨g, hg⟩

/-- The same threshold mechanism applies to finite products of selected
structured unit families, as required for paired recursion coefficients. -/
theorem mixedDualHilbert_uniform_product_gowers_threshold
    {G κ A : ℕ → Type*} {ι : Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)] [∀ w, Nonempty (A w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (S w)] (k : ℕ) (hk : 0 < k)
    (s : Finset ι) (F : ι → ∀ w, A w → κ w → G w → ℝ)
    (hF : ∀ i w a c x, |F i w a c x| ≤ 1)
    (hselected : ∀ i ∈ s, ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F i w (a w) c x) 1 zero_le_one (fun w c x => hF i w (a w) c x)) ∈
      mixedDualHilbertSubspace p S k U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in (U : Filter ℕ),
      ∀ (a : ι → A w) (g : κ w → G w → ℝ), (∀ c x, |g c x| ≤ 1) →
        weightedSubgroupGowersValue (S w) (p w) k g ≤ δ →
          |∑ c, p w c * finiteHaarMean (fun x => g c x * ∏ i ∈ s, F i w (a i) c x)| < ε := by
  let P := fun w (a : ι → A w) (c : κ w) (x : G w) => ∏ i ∈ s, F i w (a i) c x
  have hP : ∀ w a c x, |P w a c x| ≤ 1 := by
    intro w a c x
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hF i w (a i) c x)
  apply mixedDualHilbert_uniform_gowers_threshold p hs U hU S k hk P hP
  intro a
  let f := fun i => weightedHaarBoundedFamily p hs (fun w c x => F i w (a w i) c x)
    1 zero_le_one (fun w c x => hF i w (a w i) c x)
  apply mixedDualHilbert_unit_finset_product p S k U hs hk s f
  · intro i _ w c x
    exact hF i w (a w i) c x
  · intro i hi
    exact hselected i hi (fun w => a w i)
  · intro w c x
    rfl

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- The displayed lower-space containment, as supplied by a concatenation
induction hypothesis, gives one positive threshold for every recursive shift. -/
theorem mixedDualHilbert_recursive_gowers_threshold
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (S : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (S w)] (k : ℕ) (hk : 0 < k)
    (hcontain : mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U ≤
      mixedDualHilbertSubspace p S k U)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in (U : Filter ℕ),
      ∀ (a b : κ w → G w) (g : κ w → G w → ℝ), (∀ c x, |g c x| ≤ 1) →
        weightedSubgroupGowersValue (S w) (p w) k g ≤ δ →
          |∑ c, p w c * finiteHaarMean (fun x => g c x *
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
  have ht := mixedDualHilbert_uniform_gowers_threshold p hs U hU S k hk F hF
    (fun a => hcontain (hselected a))
  intro ε hε
  obtain ⟨δ, hδ, hevent⟩ := ht ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hevent] with w hw
  intro a b g hg
  exact hw (a, b) g hg

end Hindman168
