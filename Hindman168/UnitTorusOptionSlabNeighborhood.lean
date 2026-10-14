import Hindman168.UnitTorusOptionSlabMeasure

/-! Correct full torus slab-neighborhood bound. BOTH tolerance and radius
retain the fixed integer-cover/coefficient/dimension budgets before all inputs. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators

theorem unit_torus_option_slab_neighborhood (ι : Type*) [Fintype ι]
    (Z δ : ℝ) (hZ0 : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ r c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧
      ∀ (β : ℝ) (ζ : Option ι → ℝ) (ε : ℝ),
        (∀ i, |ζ i| ≤ Z) → (∀ i, |ζ i| ≤ |ζ none|) → ζ none ≠ 0 → ε ≤ c*|ζ none| →
          (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle))
            (Metric.thickening r (unitTorusFractionalSlab β ζ ε)) ≤ ENNReal.ofReal (δ/2) := by
  obtain ⟨K,hslab⟩ := unit_torus_option_slab_measure ι Z
  let C : ℝ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).card
  let D : ℝ := Fintype.card (Option ι)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hCp : 0 < C+1 := by linarith
  have hZp : 0 < Z+1 := by linarith
  have hD1 : 1 ≤ D := by
    dsimp only [D]
    exact_mod_cast (show 1 ≤ Fintype.card (Option ι) by rw [Fintype.card_option]; omega)
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  let c := δ/(32*(C+1)*(Z+1))
  let r := c/D
  have hc : 0 < c := div_pos hδ (by positivity)
  have hr : 0 < r := div_pos hc hDp
  have he : c*(C+1)*(Z+1)=δ/32 := by
    dsimp only [c]
    field_simp
  have hCc : c*(C+1) ≤ δ/32 := by
    rw [← he]
    exact le_mul_of_one_le_right (mul_nonneg hc.le hCp.le) (by linarith)
  have hZc : c*(Z+1) ≤ δ/32 := by
    have he' : c*(Z+1)*(C+1)=δ/32 := by rw [← he]; ring
    rw [← he']
    exact le_mul_of_one_le_right (mul_nonneg hc.le hZp.le) (by linarith)
  have hc1 : c ≤ δ/32 := (le_mul_of_one_le_right hc.le (by linarith : 1 ≤ C+1)).trans hCc
  have hrc : r ≤ c := div_le_self hc.le hD1
  have hr1 : r ≤ 1 := by linarith
  have hrhalf : 2*r ≤ 1 := by linarith
  have hDr : D*r=c := by dsimp only [r]; field_simp
  refine ⟨r,c,hr,hr1,hc,?_⟩
  intro β ζ ε hζ hmax hne hε
  let w := |ζ none|
  let E := ε+D*w*r
  have hw : 0 < w := abs_pos.mpr hne
  have hwZ : w ≤ Z := hζ none
  have hE : E ≤ 2*c*w := by dsimp only [E]; nlinarith [hDr]
  have hcw : c*w ≤ δ/32 :=
    (mul_le_mul_of_nonneg_left (hwZ.trans (by linarith)) hc.le).trans hZc
  have hE1 : E ≤ 1 := by linarith
  have hboundary : (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle))
      (unitTorusCoordinateBoundary r) ≤ ENNReal.ofReal (δ/16) := by
    apply (unit_torus_coordinate_boundary_measure r hrhalf).trans
    apply ENNReal.ofReal_le_ofReal
    change D*(2*r) ≤ δ/16
    nlinarith [hDr]
  have hscalar : C*(2*E/w) ≤ δ/8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hw).mpr
    have hm := mul_le_mul_of_nonneg_left hE (mul_nonneg hC zero_le_two)
    have hcB : 4*C*c ≤ δ/8 := by nlinarith
    nlinarith
  have hSlab : (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle))
      (unitTorusFractionalSlab β ζ E) ≤ ENNReal.ofReal (δ/8) :=
    (hslab β ζ E hζ hE1 hne).trans (ENNReal.ofReal_le_ofReal hscalar)
  apply (measure_mono (unit_torus_fractional_slab_neighborhood_subset β ζ ε r w hw.le hmax)).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add hboundary hSlab).trans
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ δ/16) (by positivity : 0 ≤ δ/8)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Hindman168
