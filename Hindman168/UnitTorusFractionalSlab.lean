import Hindman168.UnitTorusCoordinateBoundary
import Mathlib.Topology.MetricSpace.Thickening

/-! Actual measurable torus fractional slabs, with neighborhood growth
controlled off the TRUE coordinate-boundary strips. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators Classical

noncomputable def unitTorusFractionalExpression {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (x : UnitAddTorus ι) : ℝ :=
  β+∑ i, ζ i*unitCircleFractionalRepresentative (x i)

noncomputable def unitTorusFractionalSlab {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (ε : ℝ) : Set (UnitAddTorus ι) :=
  {x | ‖(unitTorusFractionalExpression β ζ x : UnitAddCircle)‖ ≤ ε}

theorem unit_torus_fractional_expression_measurable {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) : Measurable (unitTorusFractionalExpression β ζ) := by
  apply measurable_const.add
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (unit_circle_fractional_representative_measurable.comp (measurable_pi_apply i)))

theorem unit_torus_fractional_slab_measurable {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (ε : ℝ) : MeasurableSet (unitTorusFractionalSlab β ζ ε) :=
  (AddCircle.measurable_mk'.comp (unit_torus_fractional_expression_measurable β ζ)).norm measurableSet_Iic

theorem unit_torus_fractional_expression_difference {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (W : ℝ) (hW : ∀ i, |ζ i| ≤ W)
    {x y : UnitAddTorus ι} {r : ℝ} (hx : x ∉ unitTorusCoordinateBoundary r)
    (hxy : dist x y < r) :
    |unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y| ≤
      (Fintype.card ι : ℝ)*W*dist x y := by
  have he : unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y =
      ∑ i, ζ i*(unitCircleFractionalRepresentative (x i)-unitCircleFractionalRepresentative (y i)) := by
    dsimp only [unitTorusFractionalExpression]
    rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : (∑ i, |ζ i*(unitCircleFractionalRepresentative (x i)-unitCircleFractionalRepresentative (y i))|) ≤
      ∑ _i : ι, W*dist x y := by
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul (hW i) (unit_torus_fractional_difference_outside_boundary hx hxy i)
      (abs_nonneg _) (by exact (abs_nonneg (ζ i)).trans (hW i))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hs

theorem unit_torus_fractional_slab_neighborhood_subset {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (ε r W : ℝ) (hW : 0 ≤ W) (hζ : ∀ i, |ζ i| ≤ W) :
    Metric.thickening r (unitTorusFractionalSlab β ζ ε) ⊆
      unitTorusCoordinateBoundary r ∪ unitTorusFractionalSlab β ζ (ε+(Fintype.card ι : ℝ)*W*r) := by
  intro x hx
  by_cases hb : x ∈ unitTorusCoordinateBoundary r
  · exact Or.inl hb
  obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp hx
  apply Or.inr
  have hd := unit_torus_fractional_expression_difference β ζ W hζ hb hxy
  have hnear : ‖((unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y : ℝ) : UnitAddCircle)‖ ≤
      |unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y| :=
    (rough_mod_one_near_integer_iff _ _).mpr ⟨0,by simp⟩
  have hn : ‖(unitTorusFractionalExpression β ζ x : UnitAddCircle)‖ ≤
      ‖(unitTorusFractionalExpression β ζ y : UnitAddCircle)‖+
        ‖((unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y : ℝ) : UnitAddCircle)‖ := by
    calc
      _ = ‖(unitTorusFractionalExpression β ζ y : UnitAddCircle)+
          ((unitTorusFractionalExpression β ζ x-unitTorusFractionalExpression β ζ y : ℝ) : UnitAddCircle)‖ := by
        rw [← AddCircle.coe_add]
        congr 2
        ring
      _ ≤ _ := norm_add_le _ _
  have hr := mul_le_mul_of_nonneg_left hxy.le
    (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hW)
  exact hn.trans (add_le_add hy (hnear.trans (hd.trans hr)))

end Hindman168
