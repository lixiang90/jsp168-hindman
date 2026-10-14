import Hindman168.MixedDualInputContinuity
import Hindman168.JointMixedDualDensity

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (S : Finset (Fin d))

/-- Actual first-direction mixed duals with joint structured unit inputs,
whose distinguished nonroot input is itself a second-direction actual dual
with unit inputs retaining both structures. -/
def nestedMixedDualFamilies : Set (boundedHilbertFamilies
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :=
  {g | ∃ f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    (∀ ω w c x, |(f ω).val w (c, x)| ≤ 1) ∧
    (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U) ∧
    f S ∈ jointMixedDualFamilies p R e U Q d ∧
    ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (Q w) d
      (fun ω y => (f ω).val w (c, y)) x}

def nestedMixedDualHilbertGenerators : Set (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  hilbertFamilyToCompletion _ U '' nestedMixedDualFamilies p Q d U R e S

noncomputable def nestedMixedDualHilbertSubspace : Submodule ℝ (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  (Submodule.span ℝ (nestedMixedDualHilbertGenerators p Q d U R e S)).topologicalClosure

theorem nestedMixedDualFamilies_subset_joint :
    nestedMixedDualFamilies p Q d U R e S ⊆ jointMixedDualFamilies p Q d U R e := by
  rintro g ⟨f, hu, hf, _, hval⟩
  exact ⟨f, hu, hf, hval⟩

theorem nestedMixedDualHilbertSubspace_le_intersection
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e) :
    nestedMixedDualHilbertSubspace p Q d U R e S ≤
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  have hle : nestedMixedDualHilbertSubspace p Q d U R e S ≤ jointMixedDualHilbertSubspace p Q d U R e :=
    Submodule.topologicalClosure_mono (Submodule.span_mono
      (Set.image_mono (nestedMixedDualFamilies_subset_joint p Q d U R e S)))
  exact hle.trans (jointMixedDualHilbertSubspace_le_intersection p Q d U R e hs he)

/-- The input substitution operator sends every genuine second-direction
joint dual generator to a genuine nested dual family. -/
theorem weightedMixedDualInput_mem_nested
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (hS : S ≠ ∅)
    (f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)
    (r : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hr : r ∈ jointMixedDualFamilies p R e U Q d) :
    weightedMixedDualInput p Q d S hS
      (fun w c ω y => (f ω).val w (c, y)) (fun w c ω _ _ y => hu ω w c y) r ∈
        nestedMixedDualFamilies p Q d U R e S := by
  have hrunit := jointMixedDualFamily_unit p R e U Q d hr
  have hrint : hilbertFamilyToCompletion _ U r ∈
      mixedDualHilbertSubspace p R e U ⊓ mixedDualHilbertSubspace p Q d U :=
    jointMixedDualHilbertSubspace_le_intersection p R e U Q d hs hd
      ((Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨r, hr, rfl⟩))
  let t := fun ω : Finset (Fin d) => if ω = S then r else f ω
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro ω w c x
    by_cases hω : ω = S
    · simpa only [t, if_pos hω] using hrunit w c x
    · simpa only [t, if_neg hω] using hu ω w c x
  · intro ω hω
    by_cases heq : ω = S
    · simpa only [t, if_pos heq] using (show hilbertFamilyToCompletion _ U r ∈
        mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U from ⟨hrint.2, hrint.1⟩)
    · simpa only [t, if_neg heq] using hf ω hω
  · simpa only [t, if_pos rfl] using hr
  · intro w c x
    rw [weightedMixedDualInput_apply]
    congr 1
    funext ω y
    by_cases hω : ω = S <;> simp only [t, hω, ↓reduceIte]

end Hindman168
