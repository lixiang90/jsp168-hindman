import Hindman168.UnitTorusOptionSlabDiscrepancy
import Hindman168.UnitTorusAffineObservableInverse

/-! TRUE affine-block zero-slope detection on SAME original shifted samples.
No representative compatibility, Haar translation or interval inverse oracle. -/
namespace Hindman168
open Set
open scoped BigOperators Classical

theorem unit_torus_option_affine_slab_inverse (ι : Type*) [Fintype ι]
    (Z δ : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℕ, 0 < A ∧ ∀ (β : ℝ) (ζ γ : Option ι → ℝ)
      (a : ℕ) (ε : ℝ), (∀ i, |ζ i| ≤ Z) → (∀ i, |ζ i| ≤ |ζ none|) → ζ none ≠ 0 → ε ≤ c*|ζ none| →
        ∀ L : ℕ, 0 < L → δ*(L : ℝ) ≤ ((Finset.range L).filter (fun n : ℕ =>
          ‖((β+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
          ∃ k : Option ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
            (L : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨c,η,hc,hη,hdetect⟩ := unit_torus_option_slab_discrepancy ι Z δ hZ hδ hδ1
  obtain ⟨A,hA,hinv⟩ := unit_torus_affine_observable_inverse (Option ι) η hη
  refine ⟨c,hc,A,hA,?_⟩
  intro β ζ γ a ε hζ hmax hne hε L hL hdense
  let u : UnitAddTorus (Option ι) := fun i => (((a : ℝ)*γ i : ℝ) : UnitAddCircle)
  let f (n : ℕ) : UnitAddTorus (Option ι) := u+(fun i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle))
  have hf (n : ℕ) : f n=fun i => ((((a+n : ℕ) : ℝ)*γ i : ℝ) : UnitAddCircle) := by
    funext i
    change (((a : ℝ)*γ i : ℝ) : UnitAddCircle)+(((n : ℝ)*γ i : ℝ) : UnitAddCircle)=_
    rw [← AddCircle.coe_add]
    congr 1
    push_cast
    ring
  have hset : ((Finset.range L).filter (fun n : ℕ =>
      ‖((β+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) : ℝ) : UnitAddCircle)‖ ≤ ε)) =
      (Finset.range L).filter (fun n => f n ∈ unitTorusFractionalSlab β ζ ε) := by
    apply Finset.filter_congr
    intro n _
    rw [hf]
    simp only [unitTorusFractionalSlab,unitTorusFractionalExpression,mem_setOf_eq,
      unit_circle_fractional_representative_real]
  rw [hset] at hdense
  obtain ⟨F,hF,hbad⟩ := hdetect β ζ ε hζ hmax hne hε (Finset.range L)
    (Finset.nonempty_range_iff.mpr hL.ne') f (by simpa only [Finset.card_range] using hdense)
  exact hinv γ u L hL F hF hbad

end Hindman168
