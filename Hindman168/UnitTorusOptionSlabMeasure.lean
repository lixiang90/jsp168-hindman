import Hindman168.UnitTorusFractionalSlab
import Hindman168.UnitCircleFractionalHaarMeasure

/-! TRUE full product-circle Haar slab estimate by an actual measurable
coordinate split and Tonelli, including either sign of the selected slope.
The finite integer-cover budget precedes all offsets/coefficient inputs. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators Classical

theorem unit_torus_option_split_measure_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => UnitAddCircle))
      (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle))
      ((Measure.pi (fun _ : ι => AddCircle.haarAddCircle)).prod AddCircle.haarAddCircle) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => UnitAddCircle)
  have hi : MeasurePreserving e.symm
      ((Measure.pi (fun _ : ι => AddCircle.haarAddCircle)).prod AddCircle.haarAddCircle)
      (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle)) :=
    ⟨e.symm.measurable,Measure.pi_map_piOptionEquivProd (fun _ : Option ι => AddCircle.haarAddCircle)⟩
  exact hi.symm

theorem unit_torus_fractional_slab_fract_beta {ι : Type*} [Fintype ι]
    (β : ℝ) (ζ : ι → ℝ) (ε : ℝ) :
    unitTorusFractionalSlab β ζ ε=unitTorusFractionalSlab (Int.fract β) ζ ε := by
  ext x
  have he : unitTorusFractionalExpression β ζ x =
      unitTorusFractionalExpression (Int.fract β) ζ x+(⌊β⌋ : ℝ) := by
    dsimp only [unitTorusFractionalExpression,Int.fract]
    ring
  change ‖(_ : UnitAddCircle)‖ ≤ ε ↔ ‖(_ : UnitAddCircle)‖ ≤ ε
  rw [he,AddCircle.coe_add]
  have hz : ((⌊β⌋ : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊β⌋,by simp⟩
  rw [hz,add_zero]

theorem unit_torus_option_slab_measure (ι : Type*) [Fintype ι] (Z : ℝ) :
    ∃ K : ℕ, ∀ (β : ℝ) (ζ : Option ι → ℝ) (ε : ℝ),
      (∀ i, |ζ i| ≤ Z) → ε ≤ 1 → ζ none ≠ 0 →
        (Measure.pi (fun _ : Option ι => AddCircle.haarAddCircle)) (unitTorusFractionalSlab β ζ ε) ≤
          ENNReal.ofReal (((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ)*(2*ε/|ζ none|)) := by
  obtain ⟨K,hbound⟩ := bounded_unit_circle_fractional_slab_measure (1+(Fintype.card ι : ℝ)*Z) Z
  refine ⟨K,?_⟩
  intro β ζ ε hζ hε hne
  rw [unit_torus_fractional_slab_fract_beta]
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => UnitAddCircle)
  let θ (u : UnitAddTorus ι) := Int.fract β+∑ i, ζ (some i)*unitCircleFractionalRepresentative (u i)
  have hθ : ∀ u, |θ u| ≤ 1+(Fintype.card ι : ℝ)*Z := by
    intro u
    have hsum : |∑ i, ζ (some i)*unitCircleFractionalRepresentative (u i)| ≤ (Fintype.card ι : ℝ)*Z := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      have ht : (∑ i, |ζ (some i)*unitCircleFractionalRepresentative (u i)|) ≤ ∑ _i : ι, Z := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨h0,h1⟩ := unit_circle_fractional_representative_mem (u i)
        rw [abs_mul,abs_of_nonneg h0]
        exact (mul_le_of_le_one_right (abs_nonneg _) h1.le).trans (hζ (some i))
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using ht
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa only [abs_of_nonneg (Int.fract_nonneg β)] using (Int.fract_lt_one β).le) hsum)
  let S := e.symm ⁻¹' unitTorusFractionalSlab (Int.fract β) ζ ε
  have hS : MeasurableSet S :=
    (unit_torus_fractional_slab_measurable (Int.fract β) ζ ε).preimage e.symm.measurable
  have hp := (unit_torus_option_split_measure_preserving ι).symm.measure_preimage
    (unit_torus_fractional_slab_measurable (Int.fract β) ζ ε).nullMeasurableSet
  rw [← hp,Measure.prod_apply hS]
  have hslices (u : UnitAddTorus ι) : AddCircle.haarAddCircle (Prod.mk u ⁻¹' S) ≤
      ENNReal.ofReal (((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ)*(2*ε/|ζ none|)) := by
    have he : Prod.mk u ⁻¹' S = {v : UnitAddCircle |
        ‖((θ u+ζ none*unitCircleFractionalRepresentative v : ℝ) : UnitAddCircle)‖ ≤ ε} := by
      ext v
      change ‖(unitTorusFractionalExpression (Int.fract β) ζ (e.symm (u,v)) : UnitAddCircle)‖ ≤ ε ↔ _
      have hx : unitTorusFractionalExpression (Int.fract β) ζ (e.symm (u,v)) =
          θ u+ζ none*unitCircleFractionalRepresentative v := by
        dsimp only [unitTorusFractionalExpression,θ]
        rw [Fintype.sum_option]
        change Int.fract β+(ζ none*unitCircleFractionalRepresentative v+
          ∑ i, ζ (some i)*unitCircleFractionalRepresentative (u i)) = _
        ring
      simp only [hx,mem_setOf_eq]
    rw [he]
    exact hbound (θ u) (ζ none) ε (hθ u) (hζ none) hε hne
  calc
    _ ≤ ∫⁻ _u : UnitAddTorus ι, ENNReal.ofReal (((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ)*
        (2*ε/|ζ none|)) ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle) := lintegral_mono hslices
    _ = _ := by simp only [lintegral_const,measure_univ,mul_one]

end Hindman168
