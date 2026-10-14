import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.BigOperators.Ring.List

/-! Finite sums of products of individual nonroot coordinate functions.
The algebra is explicit, so its Stone--Weierstrass conclusion returns
actual finite recipes rather than only membership in a closed algebra. -/

namespace Hindman168
open scoped BigOperators Classical

variable {ι X K : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace K]

abbrev CornerProductRecipe (ι X : Type*) [TopologicalSpace X] :=
  List (ℝ × (ι → C(X, ℝ)))

noncomputable def cornerCoordinateProduct (vertex : ι → C(K, X))
    (factor : ι → C(X, ℝ)) : C(K, ℝ) :=
  ∏ j, (factor j).comp (vertex j)

noncomputable def CornerProductRecipe.eval (r : CornerProductRecipe ι X)
    (vertex : ι → C(K, X)) : C(K, ℝ) :=
  (r.map (fun t => t.1 • cornerCoordinateProduct vertex t.2)).sum

theorem cornerCoordinateProduct_apply (vertex : ι → C(K, X))
    (factor : ι → C(X, ℝ)) (x : K) :
    cornerCoordinateProduct vertex factor x = ∏ j, factor j (vertex j x) := by
  simp [cornerCoordinateProduct]

theorem cornerRecipe_eval_append (r s : CornerProductRecipe ι X)
    (vertex : ι → C(K, X)) : (r ++ s).eval vertex = r.eval vertex + s.eval vertex := by
  simp [CornerProductRecipe.eval]

noncomputable def CornerProductRecipe.mul (r s : CornerProductRecipe ι X) :
    CornerProductRecipe ι X :=
  r.flatMap (fun t => s.map (fun u => (t.1 * u.1, fun j => t.2 j * u.2 j)))

theorem cornerRecipe_eval_mul (r s : CornerProductRecipe ι X)
    (vertex : ι → C(K, X)) : (r.mul s).eval vertex = r.eval vertex * s.eval vertex := by
  have hprod (f g : ι → C(X, ℝ)) :
      cornerCoordinateProduct vertex (fun j => f j * g j) =
        cornerCoordinateProduct vertex f * cornerCoordinateProduct vertex g := by
    ext x
    simp [cornerCoordinateProduct, Finset.prod_mul_distrib]
  induction r with
  | nil => simp [CornerProductRecipe.mul, CornerProductRecipe.eval]
  | cons t r ih =>
    have hrow : CornerProductRecipe.eval (s.map (fun u => (t.1 * u.1, fun j => t.2 j * u.2 j))) vertex =
        (t.1 • cornerCoordinateProduct vertex t.2) * s.eval vertex := by
      clear ih r
      induction s with
      | nil => simp [CornerProductRecipe.eval]
      | cons u s ihs =>
        simp only [List.map_cons, CornerProductRecipe.eval, List.sum_cons] at ihs ⊢
        rw [hprod]
        rw [ihs]
        ext x
        simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
          smul_eq_mul]
        ring
    change CornerProductRecipe.eval ((s.map (fun u => (t.1 * u.1, fun j => t.2 j * u.2 j))) ++ CornerProductRecipe.mul r s) vertex = _
    rw [cornerRecipe_eval_append, hrow, ih]
    simp [CornerProductRecipe.eval, add_mul]

noncomputable def cornerRecipeAlgebra (vertex : ι → C(K, X)) : Subalgebra ℝ C(K, ℝ) where
  carrier := {f | ∃ r : CornerProductRecipe ι X, r.eval vertex = f}
  mul_mem' := by
    rintro f g ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r.mul s, cornerRecipe_eval_mul r s vertex⟩
  add_mem' := by
    rintro f g ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r ++ s, cornerRecipe_eval_append r s vertex⟩
  algebraMap_mem' := by
    intro a
    refine ⟨[(a, fun _ => 1)], ?_⟩
    ext x
    simp [CornerProductRecipe.eval, cornerCoordinateProduct]

theorem cornerRecipeAlgebra_coordinate_mem (vertex : ι → C(K, X))
    (j : ι) (f : C(X, ℝ)) : f.comp (vertex j) ∈ cornerRecipeAlgebra vertex := by
  refine ⟨[(1, Function.update (fun _ => (1 : C(X, ℝ))) j f)], ?_⟩
  ext x
  simp only [CornerProductRecipe.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, one_smul, cornerCoordinateProduct_apply]
  rw [Finset.prod_eq_single j]
  · simp
  · intro k _ hkj
    simp [Function.update_of_ne hkj]
  · simp

theorem cornerRecipeAlgebra_separates [T35Space X]
    (vertex : ι → C(K, X)) (hinj : Function.Injective (fun x => fun j => vertex j x)) :
    (cornerRecipeAlgebra vertex).SeparatesPoints := by
  intro x y hxy
  have hcoords : ¬ ∀ j, vertex j x = vertex j y := by
    intro h
    exact hxy (hinj (funext h))
  obtain ⟨j, hj⟩ := not_forall.mp hcoords
  obtain ⟨f, hf, hsep⟩ := separatesPoints_continuous_of_t35Space hj
  let F : C(X, ℝ) := ⟨f, hf⟩
  exact ⟨F.comp (vertex j), ⟨F.comp (vertex j), cornerRecipeAlgebra_coordinate_mem vertex j F, rfl⟩, hsep⟩

theorem cornerRecipe_uniform_approximation [CompactSpace K] [T35Space X]
    (vertex : ι → C(K, X)) (hinj : Function.Injective (fun x => fun j => vertex j x))
    (f : C(K, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : CornerProductRecipe ι X, ∀ x, |r.eval vertex x - f x| < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (cornerRecipeAlgebra vertex) (cornerRecipeAlgebra_separates vertex hinj)
    f f.continuous ε hε
  obtain ⟨r, hr⟩ := g.property
  refine ⟨r, ?_⟩
  intro x
  simpa only [hr, Real.norm_eq_abs] using hg x

end Hindman168
