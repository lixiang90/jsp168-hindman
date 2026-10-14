import Hindman168.MixedDualHilbertOrthogonality

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology symmDiff

/-- Reflection of the vertex labels realizes any vertex dual as a
genuine mixed dual with the distinguished vertex moved to the root. -/
theorem subgroupVertexDual_eq_reflected_mixedDual {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) :
    subgroupVertexDual Q d S f = subgroupMixedDualFunction Q d (fun ω => f (S ∆ ω)) := by
  funext x
  unfold subgroupVertexDual subgroupMixedDualFunction
  congr 1
  funext v
  symm
  apply Finset.prod_bij (fun ω _ => S ∆ ω)
  · intro ω hω
    have hn : S ∆ ω ≠ S := by
      intro he
      have hc := congrArg (fun T => S ∆ T) he
      simp only [symmDiff_symmDiff_cancel_left, symmDiff_self] at hc
      exact (Finset.mem_erase.mp hω).1 hc
    exact Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩
  · intro a _ b _ hab
    have hc := congrArg (fun T => S ∆ T) hab
    simpa only [symmDiff_symmDiff_cancel_left] using hc
  · intro ω hω
    refine ⟨S ∆ ω, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · intro he
      exact (Finset.mem_erase.mp hω).1 (Finset.symmDiff_eq_empty.mp he).symm
    · exact symmDiff_symmDiff_cancel_left S ω
  · intro ω _
    simp only [symmDiff_symmDiff_cancel_left]

/-- Every actual unit vertex dual belongs to the original mixed-dual
convex hull, irrespective of which cube vertex was distinguished. -/
theorem subgroupVertexDual_mem_mixedDualHull {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ ω, ω ≠ S → ∀ x, |f ω x| ≤ 1) :
    subgroupVertexDual Q d S f ∈ subgroupMixedDualHull Q d := by
  rw [subgroupVertexDual_eq_reflected_mixedDual]
  apply subgroupMixedDualFunction_mem_hull
  intro ω hω x
  apply hf (S ∆ ω) _ x
  intro he
  have hc := congrArg (fun T => S ∆ T) he
  simp only [symmDiff_symmDiff_cancel_left, symmDiff_self] at hc
  exact hω hc

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- Replacing one actual vertex by an input with the same factor
projection leaves the weighted cube average unchanged in the limit. -/
theorem mixedDualHilbert_cube_replace_vertex_tendsto_zero
    (hs : ∀ w, ∑ c, p w c = 1) (S : Finset (Fin d))
    (f g : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ ω, ω ≠ S → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (he : ∀ ω, ω ≠ S → f ω = g ω)
    (ho : hilbertFamilyToCompletion _ U (f S - g S) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ) :
    Tendsto (fun w => (∑ c, p w c * subgroupMixedCubeAverage (Q w) d
        (fun ω x => (f ω).val w (c, x))) -
      ∑ c, p w c * subgroupMixedCubeAverage (Q w) d (fun ω x => (g ω).val w (c, x)))
      (U : Filter ℕ) (𝓝 0) := by
  let a := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupVertexDual (Q w) d S (fun ω y => (f ω).val w (c, y)) x)
    1 zero_le_one (fun w c x => subgroupVertexDual_abs_le_one (Q w) d S _
      (fun ω hω y => hf ω hω w c y) x)
  have ha : hilbertFamilyToCompletion _ U a ∈ mixedDualHilbertSubspace p Q d U := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨a, ?_, rfl⟩
    intro w c
    change subgroupVertexDual (Q w) d S (fun ω y => (f ω).val w (c, y)) ∈
      subgroupMixedDualHull (Q w) d
    exact subgroupVertexDual_mem_mixedDualHull (Q w) d S _ (fun ω hω x => hf ω hω w c x)
  have hz := (Submodule.mem_orthogonal' _ _).mp ho _ ha
  have ht := weightedHaarHilbert_inner_tendsto p U (f S - g S) a
  rw [hz] at ht
  convert ht using 1
  funext w
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_sub, subgroupMixedCubeAverage_vertex_correlation (Q w) d S,
    subgroupMixedCubeAverage_vertex_correlation (Q w) d S]
  have hv : subgroupVertexDual (Q w) d S (fun ω x => (f ω).val w (c, x)) =
      subgroupVertexDual (Q w) d S (fun ω x => (g ω).val w (c, x)) := by
    apply subgroupVertexDual_congr_off_vertex
    intro ω hω
    rw [he ω hω]
  rw [← hv, ← finiteHaarMean_sub]
  congr 1
  congr 1
  funext x
  change (f S).val w (c, x) * subgroupVertexDual (Q w) d S (fun ω y => (f ω).val w (c, y)) x -
      (g S).val w (c, x) * subgroupVertexDual (Q w) d S (fun ω y => (f ω).val w (c, y)) x =
    ((f S).val w (c, x) - (g S).val w (c, x)) *
      subgroupVertexDual (Q w) d S (fun ω y => (f ω).val w (c, y)) x
  ring

/-- Simultaneous replacement of every actual cube vertex by a unit
representative of the same projection preserves its weighted limit. -/
theorem mixedDualHilbert_cube_projection_replacement_tendsto_zero
    (hs : ∀ w, ∑ c, p w c = 1)
    (f g : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ ω w c x, |(f ω).val w (c, x)| ≤ 1)
    (hg : ∀ ω w c x, |(g ω).val w (c, x)| ≤ 1)
    (ho : ∀ ω, hilbertFamilyToCompletion _ U (f ω - g ω) ∈
      (mixedDualHilbertSubspace p Q d U)ᗮ) :
    Tendsto (fun w => (∑ c, p w c * subgroupMixedCubeAverage (Q w) d
        (fun ω x => (f ω).val w (c, x))) -
      ∑ c, p w c * subgroupMixedCubeAverage (Q w) d (fun ω x => (g ω).val w (c, x)))
      (U : Filter ℕ) (𝓝 0) := by
  let mix := fun (T : Finset (Finset (Fin d))) ω => if ω ∈ T then g ω else f ω
  let C := fun (a : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) w =>
    ∑ c, p w c * subgroupMixedCubeAverage (Q w) d (fun ω x => (a ω).val w (c, x))
  have hall : ∀ T : Finset (Finset (Fin d)),
      Tendsto (fun w => C f w - C (mix T) w) (U : Filter ℕ) (𝓝 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [mix]
    | @insert S T hST ih =>
      have hr := mixedDualHilbert_cube_replace_vertex_tendsto_zero p Q d U hs S
        (mix T) (mix (insert S T))
        (fun ω _ w c x => by
          by_cases hω : ω ∈ T
          · simpa only [mix, if_pos hω] using hg ω w c x
          · simpa only [mix, if_neg hω] using hf ω w c x)
        (fun ω hω => by simp only [mix, Finset.mem_insert]; simp [hω])
        (by simpa only [mix, if_neg hST, Finset.mem_insert_self, if_true] using ho S)
      have ht := ih.add hr
      convert ht using 1
      · funext w
        change C f w - C (mix (insert S T)) w =
          (C f w - C (mix T) w) + (C (mix T) w - C (mix (insert S T)) w)
        ring
      · simp only [add_zero]
  simpa only [mix, Finset.mem_univ, if_true, C] using hall Finset.univ

end Hindman168
