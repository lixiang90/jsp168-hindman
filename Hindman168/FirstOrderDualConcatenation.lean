import Hindman168.MixedDualProjectionCompatibility
import Hindman168.SubgroupHaarComposition

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

theorem subgroupMixedDualFunction_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : Finset (Fin 1) → G → ℝ) (x : G) :
    subgroupMixedDualFunction Q 1 f x = subgroupHaarMean Q (f {0}) x := by
  have he : (Finset.univ : Finset (Finset (Fin 1))).erase ∅ = {{0}} := by decide
  simp only [subgroupMixedDualFunction, he, Finset.prod_singleton, Finset.sum_singleton]
  exact finiteHaarMean_equiv (Equiv.funUnique (Fin 1) Q) (fun a => f {0} (x + a))

theorem subgroupMixedDualHull_one_invariant {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] {f : G → ℝ} (hf : f ∈ subgroupMixedDualHull Q 1) :
    ∀ x (a : Q), f (x + a) = f x := by
  apply convexHull_min (t := {f : G → ℝ | ∀ x (a : Q), f (x + a) = f x}) ?_ ?_ hf
  · rintro f ⟨v, _, rfl⟩ x a
    rw [subgroupMixedDualFunction_one, subgroupMixedDualFunction_one]
    exact subgroupHaarMean_translate Q _ x a
  · intro f hf g hg r s _ _ _ x a
    change r * f (x + a) + s * g (x + a) = r * f x + s * g x
    rw [hf x a, hg x a]

theorem subgroupMixedDualHull_one_of_unit_invariant {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hinv : ∀ x (a : Q), f (x + a) = f x) : f ∈ subgroupMixedDualHull Q 1 := by
  have hm := subgroupMixedDualFunction_mem_hull Q 1 (fun _ => f) (fun _ _ => hf)
  have he : subgroupMixedDualFunction Q 1 (fun _ => f) = f := by
    funext x
    rw [subgroupMixedDualFunction_one]
    change finiteHaarMean (fun a : Q => f (x + a)) = f x
    simp only [hinv, finiteHaarMean_const]
  rwa [he] at hm

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (U : Ultrafilter ℕ)

/-- When the actual Haar average is represented by a dual-hull family, its image
is the first-order dual projection. The input needs only bounded L2 norms. -/
theorem mixedDualHilbert_first_projection
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c, (fun x => g.val w (c, x)) ∈ subgroupMixedDualHull (Q w) 1)
    (heq : ∀ w c x, g.val w (c, x) = subgroupHaarMean (Q w) (fun y => f.val w (c, y)) x) :
    (mixedDualHilbertSubspace p Q 1 U).starProjection (hilbertFamilyToCompletion _ U f) =
      hilbertFamilyToCompletion _ U g := by
  have hgm : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertGenerators p Q 1 U := ⟨g, hg, rfl⟩
  apply Submodule.eq_starProjection_of_mem_orthogonal
    ((Submodule.le_topologicalClosure _) (Submodule.subset_span hgm))
  have ho : hilbertFamilyToCompletion _ U (f - g) ∈ (mixedDualHilbertSubspace p Q 1 U)ᗮ := by
    rw [mixedDualHilbertSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨t, ht, rfl⟩ := hz
      have hv (w : ℕ) (c : κ w) :
          subgroupHaarMean (Q w) (fun y => t.val w (c, y)) = (fun y => t.val w (c, y)) := by
        funext x
        change finiteHaarMean (fun a : Q w => t.val w (c, x + a)) = t.val w (c, x)
        simp only [subgroupMixedDualHull_one_invariant (Q w) (ht w c), finiteHaarMean_const]
      have hc (w : ℕ) (c : κ w) : finiteHaarMean (fun x => f.val w (c, x) * t.val w (c, x)) =
          finiteHaarMean (fun x => g.val w (c, x) * t.val w (c, x)) := by
        have ha := subgroupHaarMean_self_adjoint (Q w) (fun y => f.val w (c, y)) (fun y => t.val w (c, y))
        rw [hv] at ha
        simpa only [heq] using ha.symm
      have hzmean (w : ℕ) : (∑ c, p w c * finiteHaarMean
          (fun x => (f - g).val w (c, x) * t.val w (c, x))) = 0 := by
        change (∑ c, p w c * finiteHaarMean (fun x => (f.val w (c, x) - g.val w (c, x)) * t.val w (c, x))) = 0
        simp only [sub_mul, finiteHaarMean_sub, hc, sub_self, mul_zero, Finset.sum_const_zero]
      exact tendsto_nhds_unique (weightedHaarHilbert_inner_tendsto p U (f - g) t)
        (by simpa only [hzmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (U : Filter ℕ) (𝓝 0)))
    | zero => exact inner_zero_right _
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]
  have he : hilbertFamilyToCompletion _ U (f - g) =
      hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U g :=
    (hilbertFamilyCompletionLinearMap _ U).map_sub f g
  rwa [he] at ho

/-- One actual unit-bounded Haar representative for the first-order projection. -/
theorem mixedDualHilbert_first_projection_representative
    (hs : ∀ w, ∑ c, p w c = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, |f.val w (c, x)| ≤ 1) :
    ∃ g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, |g.val w (c, x)| ≤ 1) ∧
      (∀ w c x, g.val w (c, x) = subgroupHaarMean (Q w) (fun y => f.val w (c, y)) x) ∧
      hilbertFamilyToCompletion _ U g =
        (mixedDualHilbertSubspace p Q 1 U).starProjection (hilbertFamilyToCompletion _ U f) := by
  let g := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupHaarMean (Q w) (fun y => f.val w (c, y)) x) 1 zero_le_one
    (fun w c x => finiteHaarMean_abs_le_one _ (fun a : Q w => hf w c (x + a)))
  have hg : ∀ w c, (fun x => g.val w (c, x)) ∈ subgroupMixedDualHull (Q w) 1 := by
    intro w c
    have hm := subgroupMixedDualFunction_mem_hull (Q w) 1 (fun _ y => f.val w (c, y))
      (fun _ _ y => hf w c y)
    have hh : (fun x => g.val w (c, x)) = subgroupMixedDualFunction (Q w) 1 (fun _ y => f.val w (c, y)) := by
      funext x
      exact (subgroupMixedDualFunction_one (Q w) (fun _ y => f.val w (c, y)) x).symm
    rw [hh]
    exact hm
  exact ⟨g, fun w c x => finiteHaarMean_abs_le_one _ (fun a : Q w => hf w c (x + a)),
    fun _ _ _ => rfl, (mixedDualHilbert_first_projection p Q U f g hg (fun _ _ _ => rfl)).symm⟩


theorem mixedDualHilbert_first_subgroup_antitone
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (hQR : ∀ w, Q w ≤ R w) :
    mixedDualHilbertSubspace p R 1 U ≤ mixedDualHilbertSubspace p Q 1 U := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro z ⟨f, hf, rfl⟩
  refine ⟨f, ?_, rfl⟩
  intro w c
  apply subgroupMixedDualHull_one_of_unit_invariant (Q w) (fun x => f.val w (c, x))
    (fun x => subgroupMixedDualHull_abs_le_one (R w) 1 (hf w c) x)
  intro x a
  exact subgroupMixedDualHull_one_invariant (R w) (hf w c) x ⟨a, hQR w a.property⟩

/-- The base concatenation containment for the actual closed spaces, without
requiring the ultrafilter to contain all tails. -/
theorem mixedDualHilbert_first_concatenation
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)]
    [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))] :
    mixedDualHilbertSubspace p Q 1 U ⊓ mixedDualHilbertSubspace p R 1 U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) 1 U := by
  let W := mixedDualHilbertSubspace p R 1 U
  let S := mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) 1 U
  let T := S.comap W.starProjection.toLinearMap
  have hT : IsClosed (T : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)) :=
    (Submodule.span ℝ (mixedDualHilbertGenerators p (fun w => Q w ⊔ R w) 1 U)).isClosed_topologicalClosure.preimage
      W.starProjection.continuous
  have hspan : Submodule.span ℝ (mixedDualHilbertGenerators p Q 1 U) ≤ T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f, hf, rfl⟩
    have hunit : ∀ w c x, |f.val w (c, x)| ≤ 1 :=
      fun w c x => subgroupMixedDualHull_abs_le_one (Q w) 1 (hf w c) x
    obtain ⟨g, _, heq, hp⟩ := mixedDualHilbert_first_projection_representative p R U hs f hunit
    have hQ (w : ℕ) (c : κ w) : subgroupHaarMean (Q w) (fun y => f.val w (c, y)) = (fun y => f.val w (c, y)) := by
      funext x
      change finiteHaarMean (fun a : Q w => f.val w (c, x + a)) = f.val w (c, x)
      simp only [subgroupMixedDualHull_one_invariant (Q w) (hf w c), finiteHaarMean_const]
    have hsum (w : ℕ) (c : κ w) (x : G w) :
        subgroupHaarMean (Q w ⊔ R w) (fun y => f.val w (c, y)) x =
          subgroupHaarMean (R w) (fun y => f.val w (c, y)) x := by
      rw [← subgroupHaarMean_sup, subgroupHaarMean_commute, hQ]
    have hg : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertGenerators p (fun w => Q w ⊔ R w) 1 U := by
      refine ⟨g, ?_, rfl⟩
      intro w c
      have hm := subgroupMixedDualFunction_mem_hull (Q w ⊔ R w) 1 (fun _ y => f.val w (c, y))
        (fun _ _ y => hunit w c y)
      have he : (fun x => g.val w (c, x)) = subgroupMixedDualFunction (Q w ⊔ R w) 1 (fun _ y => f.val w (c, y)) := by
        funext x
        rw [heq, subgroupMixedDualFunction_one, hsum]
      rwa [← he] at hm
    change W.starProjection (hilbertFamilyToCompletion _ U f) ∈ S
    rw [← hp]
    exact (Submodule.le_topologicalClosure _) (Submodule.subset_span hg)
  have hmap : mixedDualHilbertSubspace p Q 1 U ≤ T :=
    (Submodule.span ℝ (mixedDualHilbertGenerators p Q 1 U)).topologicalClosure_minimal hspan hT
  intro z hz
  have h := hmap hz.1
  change W.starProjection z ∈ S at h
  rwa [Submodule.starProjection_eq_self_iff.mpr hz.2] at h

theorem mixedDualHilbert_first_intersection_eq_sum
    (hs : ∀ w, ∑ c, p w c = 1)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)]
    [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))] :
    mixedDualHilbertSubspace p Q 1 U ⊓ mixedDualHilbertSubspace p R 1 U =
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) 1 U := by
  apply le_antisymm (mixedDualHilbert_first_concatenation p Q U hs R)
  exact le_inf (mixedDualHilbert_first_subgroup_antitone p Q U (fun w => Q w ⊔ R w) (fun _ => le_sup_left))
    (mixedDualHilbert_first_subgroup_antitone p R U (fun w => Q w ⊔ R w) (fun _ => le_sup_right))

end Hindman168
