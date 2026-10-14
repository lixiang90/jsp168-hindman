import Hindman168.NativeRealResidualLargeEvent

/-! Original integer cube endpoints give the exact original REAL residual
geometry before any ceil resampling. Counts and means are not changed. -/
namespace Hindman168

theorem original_integer_residual_box_geometry {κ : Type*}
    (lo hi a : κ → ℤ) (q : ℕ) (hq : 0 < q) (Z c A C : ℝ)
    (hZ : (q : ℝ) ≤ Z)
    (ha : ∀ j, 0 ≤ a j ∧ a j < (q : ℤ))
    (hgeom : ∀ j, |(lo j : ℝ)| ≤ A*Z ∧ |(hi j : ℝ)| ≤ A*Z ∧
      c*Z ≤ (hi j : ℝ)-(lo j : ℝ) ∧ (hi j : ℝ)-(lo j : ℝ) ≤ C*Z) :
    ∀ j, c*(Z/(q : ℝ)) ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ max C (A+1)*(Z/(q : ℝ)) ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ max C (A+1)*(Z/(q : ℝ)) ∧
      |(hi j-(a j : ℝ))/(q : ℝ)| ≤ max C (A+1)*(Z/(q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hZpos : 0 < Z := hqR.trans_le hZ
  intro j
  have haj : (0 : ℝ) ≤ a j := by exact_mod_cast (ha j).1
  have hajq : (a j : ℝ) < q := by exact_mod_cast (ha j).2
  have hd : (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ)=
      ((hi j : ℝ)-(lo j : ℝ))/(q : ℝ) := by ring
  have hupper : C*Z ≤ max C (A+1)*Z := mul_le_mul_of_nonneg_right (le_max_left _ _) hZpos.le
  have hendpoint (t : ℤ) (ht : |(t : ℝ)| ≤ A*Z) :
      |((t : ℝ)-(a j : ℝ))/(q : ℝ)| ≤ max C (A+1)*(Z/(q : ℝ)) := by
    rw [abs_div,abs_of_pos hqR,←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hqR.le
    have he := abs_sub (t : ℝ) (a j : ℝ)
    rw [abs_of_nonneg haj] at he
    have he' := he.trans (add_le_add ht hajq.le)
    have hm : (A+1)*Z ≤ max C (A+1)*Z := mul_le_mul_of_nonneg_right (le_max_right _ _) hZpos.le
    nlinarith
  refine ⟨?_,?_,hendpoint _ (hgeom j).1,hendpoint _ (hgeom j).2.1⟩
  · rw [hd,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hgeom j).2.2.1 hqR.le
  · rw [hd,←mul_div_assoc]
    exact div_le_div_of_nonneg_right ((hgeom j).2.2.2.trans hupper) hqR.le

end Hindman168
