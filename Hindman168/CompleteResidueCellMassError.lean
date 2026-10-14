import Hindman168.CompleteResidueCellMass

namespace Hindman168
open scoped BigOperators

theorem completeResidueCell_integerMass_conditional (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)) (F : ℤ → ℝ) :
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) /
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y) =
    (∑ t : Fin q, (1 / (completeResidueCellPoint k M q r t : ℝ)) *
      F (completeResidueCellPoint k M q r t)) /
    (∑ t : Fin q, 1 / (completeResidueCellPoint k M q r t : ℝ)) := by
  have hd := completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi (fun _ => 1)
  simp only [mul_one, if_pos hr] at hd
  rw [completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi F, if_pos hr, hd]
  exact div_div_div_cancel_right₀ (ne_of_gt hZ) _ _

theorem completeResidueCell_integerMass_error (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) (F : ℤ → ℝ) (hF : ∀ y, |F y| ≤ 1) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) /
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y) -
    finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t))| ≤
      (M * q : ℕ) / ((k : ℝ) * (M * q : ℕ)) := by
  rw [completeResidueCell_integerMass_conditional X W k M q hM hWM r hr hZ hlo hhi]
  have he := completeResidueCell_harmonic_error k M q hM hq r F hF hA
  rw [completeResidueCell_sum k M q hM, completeResidueCell_sum k M q hM] at he
  exact he

end Hindman168
