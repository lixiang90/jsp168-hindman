import Hindman168.NilCornerRecipe

/-! Normalize every continuous coordinate factor to absolute value at most
one, moving all scaling into finite scalar coefficients. The resulting
coefficient mass bounds the recipe everywhere, including bad cubes. -/

namespace Hindman168
open scoped BigOperators Classical

variable {ι X K : Type*} [Fintype ι] [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace K]

def CornerProductRecipe.Bounded (r : CornerProductRecipe ι X) : Prop :=
  ∀ t ∈ r, ∀ j x, |t.2 j x| ≤ 1

noncomputable def cornerFactorScale (f : C(X, ℝ)) : ℝ := max 1 ‖f‖

noncomputable def cornerNormalizedFactor (f : C(X, ℝ)) : C(X, ℝ) :=
  (cornerFactorScale f)⁻¹ • f

theorem cornerFactorScale_pos (f : C(X, ℝ)) : 0 < cornerFactorScale f := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem cornerNormalizedFactor_abs_le (f : C(X, ℝ)) (x : X) :
    |cornerNormalizedFactor f x| ≤ 1 := by
  have hp := cornerFactorScale_pos f
  have hfn : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hf : |f x| ≤ cornerFactorScale f := hfn.trans (le_max_right _ _)
  simpa only [cornerNormalizedFactor, ContinuousMap.smul_apply, smul_eq_mul,
    abs_mul, abs_inv, abs_of_pos hp, div_eq_inv_mul] using (div_le_one hp).mpr hf

noncomputable def CornerProductRecipe.normalize (r : CornerProductRecipe ι X) :
    CornerProductRecipe ι X :=
  r.map (fun t => (t.1 * ∏ j, cornerFactorScale (t.2 j),
    fun j => cornerNormalizedFactor (t.2 j)))

theorem cornerRecipe_normalize_bounded (r : CornerProductRecipe ι X) :
    (r.normalize).Bounded := by
  intro t ht j x
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  exact cornerNormalizedFactor_abs_le (u.2 j) x

theorem cornerRecipe_normalize_eval (r : CornerProductRecipe ι X)
    (vertex : ι → C(K, X)) : r.normalize.eval vertex = r.eval vertex := by
  have ht (t : ℝ × (ι → C(X, ℝ))) :
      (t.1 * ∏ j, cornerFactorScale (t.2 j)) •
        cornerCoordinateProduct vertex (fun j => cornerNormalizedFactor (t.2 j)) =
      t.1 • cornerCoordinateProduct vertex t.2 := by
    ext x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, cornerCoordinateProduct_apply,
      cornerNormalizedFactor]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (cornerFactorScale_pos _)), one_mul]
  induction r with
  | nil => rfl
  | cons t r ih =>
    simp only [CornerProductRecipe.normalize, List.map_cons, CornerProductRecipe.eval,
      List.sum_cons] at ih ⊢
    rw [ht, ih]

noncomputable def CornerProductRecipe.coefficientMass (r : CornerProductRecipe ι X) : ℝ :=
  (r.map (fun t => |t.1|)).sum

omit [Fintype ι] [CompactSpace X] in
theorem cornerRecipe_coefficientMass_nonneg (r : CornerProductRecipe ι X) :
    0 ≤ r.coefficientMass := by
  induction r with
  | nil => exact le_refl 0
  | cons t r ih =>
    exact add_nonneg (abs_nonneg t.1) ih

omit [CompactSpace X] in
theorem cornerRecipe_bounded_eval_abs_le (r : CornerProductRecipe ι X) (hr : r.Bounded)
    (vertex : ι → C(K, X)) (x : K) : |r.eval vertex x| ≤ r.coefficientMass := by
  induction r with
  | nil => simp [CornerProductRecipe.eval, CornerProductRecipe.coefficientMass]
  | cons t r ih =>
    have ht : ∀ j, |t.2 j (vertex j x)| ≤ 1 := fun j => hr t (by simp) j _
    have hp : |cornerCoordinateProduct vertex t.2 x| ≤ 1 := by
      rw [cornerCoordinateProduct_apply, Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => ht j)
    have htail : CornerProductRecipe.Bounded r := fun u hu => hr u (by simp [hu])
    simp only [CornerProductRecipe.eval, List.map_cons, List.sum_cons,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      CornerProductRecipe.coefficientMass]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hp (abs_nonneg t.1)).trans_eq (mul_one _))
      (ih htail))

theorem cornerRecipe_bounded_uniform_approximation [CompactSpace K] [T35Space X]
    (vertex : ι → C(K, X)) (hinj : Function.Injective (fun x => fun j => vertex j x))
    (f : C(K, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : CornerProductRecipe ι X, r.Bounded ∧ ∀ x, |r.eval vertex x - f x| < ε := by
  obtain ⟨r, hr⟩ := cornerRecipe_uniform_approximation vertex hinj f ε hε
  exact ⟨r.normalize, cornerRecipe_normalize_bounded r,
    by simpa only [cornerRecipe_normalize_eval] using hr⟩

end Hindman168
