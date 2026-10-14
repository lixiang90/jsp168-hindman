import Hindman168.NestedMixedDualCoefficientStructure
import Hindman168.MixedDualUniformGowersThreshold

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- Under both displayed lower-order containments, a single eventual positive
Gowers threshold tests every pair of actual double-recursion coefficients.
Every shift is independently chosen at each stage and original cell. -/
theorem mixedDualHilbert_nested_pair_gowers_threshold
    {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
    [∀ w, Fintype (κ w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (Q R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] [∀ w, Fintype (R w)] (d e : ℕ)
    (S : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (S w)] (k : ℕ) (hk : 0 < k)
    (hleft : 0 < d → mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R (e + 1) U ≤
      mixedDualHilbertSubspace p S k U)
    (hright : 0 < e → mixedDualHilbertSubspace p R e U ⊓ mixedDualHilbertSubspace p Q (d + 1) U ≤
      mixedDualHilbertSubspace p S k U)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (u : Finset (Fin (e + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hfunit : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (huunit : ∀ ω, ω ≠ ∅ → ∀ w c x, |(u ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R (e + 1) U)
    (hu : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (u ω) ∈ mixedDualHilbertSubspace p Q (d + 1) U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in (U : Filter ℕ),
      ∀ (n m h j : Fin 2 → κ w → G w) (g : κ w → G w → ℝ),
        (∀ c x, |g c x| ≤ 1) → weightedSubgroupGowersValue (S w) (p w) k g ≤ δ →
          |∑ c, p w c * finiteHaarMean (fun x => g c x * ∏ i : Fin 2,
            subgroupNestedMixedDualCoefficient (Q w) (R w) d e
              (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y))
              (n i c) (m i c) (h i c) (j i c) x)| < ε := by
  let A := fun w => (κ w → G w) × (κ w → G w) × (κ w → G w) × (κ w → G w)
  let F := fun w (a : A w) (c : κ w) (x : G w) =>
    subgroupNestedMixedDualCoefficient (Q w) (R w) d e
      (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y))
      (a.1 c) (a.2.1 c) (a.2.2.1 c) (a.2.2.2 c) x
  have hF : ∀ w a c x, |F w a c x| ≤ 1 := fun w a c x =>
    subgroupNestedMixedDualCoefficient_abs_le_one (Q w) (R w) d e _ _
      (fun ω hω y => hfunit ω hω w c y) (fun ω hω y => huunit ω hω w c y) _ _ _ _ x
  have hselected : ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)) ∈
        mixedDualHilbertSubspace p S k U := by
    intro a
    obtain ⟨C, _, hCm, hCv⟩ := mixedDualHilbert_nested_coefficient_target p Q d U hs R e S k hk
      hleft hright f u hfunit huunit hf hu
      (fun w => (a w).1) (fun w => (a w).2.1)
      (fun w => (a w).2.2.1) (fun w => (a w).2.2.2)
    have heq : C = weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x) := by
      apply Subtype.ext
      funext w z
      exact hCv w z.1 z.2
    rwa [← heq]
  have ht := mixedDualHilbert_uniform_product_gowers_threshold p hs U hU S k hk
    (Finset.univ : Finset (Fin 2)) (fun _ => F) (fun _ => hF) (fun _ _ => hselected)
  intro ε hε
  obtain ⟨δ, hδ, hevent⟩ := ht ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hevent] with w hw
  intro n m h j g hg
  exact hw (fun i => (n i, m i, h i, j i)) g hg

end Hindman168
