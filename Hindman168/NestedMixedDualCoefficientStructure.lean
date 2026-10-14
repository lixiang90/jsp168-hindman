import Hindman168.NestedMixedDualRecursion
import Hindman168.NestedMixedDualDensity
import Hindman168.MixedDualRecursiveLocalization

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- A lower recursive coefficient, including its zero-degree case, lies in
the target factor under the explicitly displayed lower-degree containment.
Its evaluation shift may vary by stage and original cell. -/
theorem mixedDualHilbert_recursive_coefficient_target
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (S : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (S w)] (k : ℕ) (hk : 0 < k)
    (hcontain : 0 < d → mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U ≤
      mixedDualHilbertSubspace p S k U)
    (f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U)
    (a b t : ∀ w, κ w → G w) :
    ∃ C : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |C.val w (c, x)| ≤ 1) ∧
      hilbertFamilyToCompletion _ U C ∈ mixedDualHilbertSubspace p S k U ∧
      ∀ w c x, C.val w (c, x) = subgroupMixedDualRecursiveCoefficient (Q w) d
        (fun ω y => (f ω).val w (c, y)) (a w c) (b w c) (x + t w c) := by
  by_cases hd : d = 0
  · subst d
    let C := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => (1 : ℝ))
      1 zero_le_one (by simp)
    refine ⟨C, ?_, ?_, ?_⟩
    · intro w c x
      change |(1 : ℝ)| ≤ 1
      norm_num
    · exact (Submodule.le_topologicalClosure _) (Submodule.subset_span
        ⟨C, fun w _ => subgroupMixedDualHull_one_mem (S w) k, rfl⟩)
    · intro w c x
      exact (subgroupMixedDualRecursiveCoefficient_zero (Q w) _ _ _ _).symm
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨C, hCu, hCm, hCv⟩ := mixedDualHilbert_recursive_coefficient_localized p Q d U hs R e he f hu hf a b
    refine ⟨weightedHaarTranslation p t C, ?_, ?_, ?_⟩
    · intro w c x
      exact hCu w c (x + t w c)
    · exact mixedDualHilbert_translation_closed p S k U hs hk t C (hcontain hdpos hCm)
    · intro w c x
      exact hCv w c (x + t w c)

/-- The actual two-level coefficient is unit bounded and belongs to the
target factor when both lower intersections have the displayed containments.
No higher-order concatenation statement is assumed without these premises. -/
theorem mixedDualHilbert_nested_coefficient_target
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)
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
    (hu : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (u ω) ∈ mixedDualHilbertSubspace p Q (d + 1) U)
    (n m h j : ∀ w, κ w → G w) :
    ∃ C : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |C.val w (c, x)| ≤ 1) ∧
      hilbertFamilyToCompletion _ U C ∈ mixedDualHilbertSubspace p S k U ∧
      ∀ w c x, C.val w (c, x) = subgroupNestedMixedDualCoefficient (Q w) (R w) d e
        (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y))
        (n w c) (m w c) (h w c) (j w c) x := by
  obtain ⟨C, hCu, hCm, hCv⟩ := mixedDualHilbert_recursive_coefficient_target
    p Q d U hs R (e + 1) (Nat.succ_pos _) S k hk hleft f hfunit hf n h m
  obtain ⟨D, hDu, hDm, hDv⟩ := mixedDualHilbert_recursive_coefficient_target
    p R e U hs Q (d + 1) (Nat.succ_pos _) S k hk hright u huunit hu m j h
  let P := weightedHaarMultiplier p (fun w c x => C.val w (c, x)) hCu D
  refine ⟨P, ?_, mixedDualHilbert_structured_product_closed p S k U hs hk C hCu hCm D hDm, ?_⟩
  · intro w c x
    change |C.val w (c, x) * D.val w (c, x)| ≤ 1
    rw [abs_mul]
    exact (mul_le_mul (hCu w c x) (hDu w c x) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro w c x
    change C.val w (c, x) * D.val w (c, x) = _
    rw [hCv, hDv]
    rfl

/-- Every genuine nested generator at the distinguished singleton vertex
has actual unit inputs in both factors and the exact two-level expansion. -/
theorem nestedMixedDualFamily_translate_expansion
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)
    {g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))}
    (hg : g ∈ nestedMixedDualFamilies p Q (d + 1) U R (e + 1) {0}) :
    ∃ f : Finset (Fin (d + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    ∃ u : Finset (Fin (e + 1)) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ ω w c x, |(f ω).val w (c, x)| ≤ 1) ∧
      (∀ ω w c x, |(u ω).val w (c, x)| ≤ 1) ∧
      (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈
        mixedDualHilbertSubspace p Q (d + 1) U ⊓ mixedDualHilbertSubspace p R (e + 1) U) ∧
      (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (u ω) ∈
        mixedDualHilbertSubspace p R (e + 1) U ⊓ mixedDualHilbertSubspace p Q (d + 1) U) ∧
      ∀ w c (n : Q w) (m : R w) x, g.val w (c, x + n + m) =
        finiteHaarMean (fun h : Q w => finiteHaarMean (fun j : R w =>
          subgroupNestedMixedDualCoefficient (Q w) (R w) d e
            (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y)) n m h j x *
              (u {0}).val w (c, x + h + j))) := by
  obtain ⟨f, hfunit, hf, hr, hval⟩ := hg
  obtain ⟨u, huunit, hu, hroot⟩ := hr
  refine ⟨f, u, hfunit, huunit, hf, hu, ?_⟩
  intro w c n m x
  rw [hval]
  exact subgroupMixedDualFunction_nested_translate_expansion (Q w) (R w) d e
    (fun ω y => (f ω).val w (c, y)) (fun ω y => (u ω).val w (c, y)) (hroot w c) n m x

end Hindman168
