import Hindman168.RoughCompactParameterFreezing

namespace Hindman168
open Set

theorem rough_uniform_lipschitz_approximation {X : Type*}
    [PseudoMetricSpace X] [Nonempty X] (B δ ε : ℝ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    ∃ K : NNReal, ∀ f : X → ℝ, (∀ x, |f x| ≤ B) →
      (∀ x y, dist x y < δ → |f x - f y| ≤ ε) →
      ∃ g : X → ℝ, LipschitzWith K g ∧
        (∀ x, |f x - g x| ≤ ε) ∧ (∀ x, |g x| ≤ B) := by
  let K : NNReal := ⟨2 * B / δ, div_nonneg (by positivity) hδ.le⟩
  refine ⟨K, ?_⟩
  intro f hf hm
  let g : X → ℝ := fun x => ⨅ y : X, f y + (K : ℝ) * dist x y
  have hscale : (K : ℝ) * δ = 2 * B := by
    dsimp only [K]
    exact div_mul_cancel₀ _ hδ.ne'
  have hbelow : ∀ x, BddBelow (range (fun y : X => f y + (K : ℝ) * dist x y)) := by
    intro x
    refine ⟨-B, ?_⟩
    rintro z ⟨y, rfl⟩
    have hfy := (abs_le.mp (hf y)).1
    have hpos : 0 ≤ (K : ℝ) * dist x y := mul_nonneg K.coe_nonneg dist_nonneg
    linarith
  have hgup (x : X) : g x ≤ f x := by
    simpa only [dist_self, mul_zero, add_zero] using ciInf_le (hbelow x) x
  have hglow (x : X) : f x - ε ≤ g x := by
    apply le_ciInf
    intro y
    by_cases hnear : dist x y < δ
    · have h := (abs_le.mp (hm x y hnear)).2
      have hpos : 0 ≤ (K : ℝ) * dist x y := mul_nonneg K.coe_nonneg dist_nonneg
      linarith
    · have hfar : δ ≤ dist x y := le_of_not_gt hnear
      have hdist : 2 * B ≤ (K : ℝ) * dist x y := by
        rw [← hscale]
        exact mul_le_mul_of_nonneg_left hfar K.coe_nonneg
      have hfx := (abs_le.mp (hf x)).2
      have hfy := (abs_le.mp (hf y)).1
      linarith
  have hLip : LipschitzWith K g := by
    apply LipschitzWith.of_le_add_mul
    intro x y
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro z
    rw [sub_le_iff_le_add]
    calc
      g x ≤ f z + (K : ℝ) * dist x z := ciInf_le (hbelow x) z
      _ ≤ f z + (K : ℝ) * dist y z + (K : ℝ) * dist x y := by
        rw [add_assoc, ← mul_add, add_comm (dist y z)]
        gcongr
        exact dist_triangle _ _ _
  refine ⟨g, hLip, ?_, ?_⟩
  · intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (hgup x))]
    linarith [hglow x]
  · intro x
    apply abs_le.mpr
    refine ⟨?_, (hgup x).trans (abs_le.mp (hf x)).2⟩
    apply le_ciInf
    intro y
    have hfy := (abs_le.mp (hf y)).1
    have hpos : 0 ≤ (K : ℝ) * dist x y := mul_nonneg K.coe_nonneg dist_nonneg
    linarith

end Hindman168
