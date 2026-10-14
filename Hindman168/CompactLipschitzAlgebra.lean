import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Complex.Basic

/-! Actual complex continuous Lipschitz functions form a star algebra
on a compact metric space; actual distance functions separate points. -/

namespace Hindman168
open scoped NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem compact_lipschitz_mul (F G : C(X, ℂ)) (K L : ℝ≥0)
    (hF : LipschitzWith K F) (hG : LipschitzWith L G) :
    LipschitzWith (‖F‖₊*L + K*‖G‖₊) (F*G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ContinuousMap.mul_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]
  have hf := hF.dist_le_mul x y
  have hg := hG.dist_le_mul x y
  simp only [dist_eq_norm] at hf hg
  calc
    _ = ‖F x*(G x-G y)+(F x-F y)*G y‖ := by congr 1; ring
    _ ≤ ‖F x*(G x-G y)‖+‖(F x-F y)*G y‖ := norm_add_le _ _
    _ = ‖F x‖*‖G x-G y‖+‖F x-F y‖*‖G y‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖F‖*((L : ℝ)*dist x y) + ((K : ℝ)*dist x y)*‖G‖ :=
      add_le_add (mul_le_mul (F.norm_coe_le_norm x) hg (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hf (G.norm_coe_le_norm y) (norm_nonneg _) (by positivity))
    _ = _ := by ring

noncomputable def compactLipschitzSubalgebra (X : Type*) [MetricSpace X] [CompactSpace X] :
    Subalgebra ℂ C(X, ℂ) where
  carrier := {F | ∃ K : ℝ≥0, LipschitzWith K F}
  zero_mem' := ⟨0, LipschitzWith.of_dist_le_mul (fun x y => by simp)⟩
  one_mem' := ⟨0, LipschitzWith.of_dist_le_mul (fun x y => by simp)⟩
  add_mem' := by
    rintro F G ⟨K,hF⟩ ⟨L,hG⟩
    exact ⟨K+L, hF.add hG⟩
  mul_mem' := by
    rintro F G ⟨K,hF⟩ ⟨L,hG⟩
    exact ⟨‖F‖₊*L+K*‖G‖₊, compact_lipschitz_mul F G K L hF hG⟩
  algebraMap_mem' c := ⟨0, LipschitzWith.of_dist_le_mul (fun x y => by simp)⟩

noncomputable def compactLipschitzStarSubalgebra (X : Type*) [MetricSpace X] [CompactSpace X] :
    StarSubalgebra ℂ C(X, ℂ) where
  toSubalgebra := compactLipschitzSubalgebra X
  star_mem' := by
    rintro F ⟨K,hF⟩
    refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    change dist (star (F x)) (star (F y)) ≤ (K : ℝ)*dist x y
    rw [Complex.star_def, Complex.dist_conj_conj]
    exact hF.dist_le_mul x y

theorem compact_lipschitz_star_subalgebra_separates (X : Type*) [MetricSpace X] [CompactSpace X] :
    (compactLipschitzStarSubalgebra X).SeparatesPoints := by
  intro x y hxy
  let F : C(X, ℂ) := ⟨fun z => (dist z x : ℂ),
    Complex.continuous_ofReal.comp (continuous_id.dist continuous_const)⟩
  have hF : LipschitzWith 1 F := by
    apply LipschitzWith.mk_one
    intro a b
    change dist (Complex.ofReal (dist a x)) (Complex.ofReal (dist b x)) ≤ dist a b
    rw [Complex.isometry_ofReal.dist_eq]
    exact (LipschitzWith.dist_left x).dist_le_mul a b |>.trans (by simp)
  refine ⟨(F : X → ℂ), ⟨F, ⟨1,hF⟩, rfl⟩, ?_⟩
  change Complex.ofReal (dist x x) ≠ Complex.ofReal (dist y x)
  intro he
  have hd := Complex.ofReal_injective he
  rw [dist_self] at hd
  exact hxy (dist_eq_zero.mp hd.symm).symm

end Hindman168
