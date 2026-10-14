import Hindman168.PositiveColorCountExtraction
import Hindman168.PrincipalWeightedColorCounts
import Hindman168.MaskSubsetScaledForms

/-!
# The final extraction for the original principal weighted count

This is the actual count defined in `PrincipalWeightedColorCounts`, with
its original divisor factors and integer normalized forms. Positivity is
an explicit input, not a theorem claimed by this module. The arithmetic
conditions hold eventually by the existing master-parameter theorems.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- The paper's count with one common color is exactly the finite color
integrand used in the extraction argument. -/
theorem principalWeightedColorCount_extraction_eq {n m r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r)
    (κ : Fin r) (w : ℕ) :
    principalWeightedColorCount C M e F a χ (fun _ => κ) κ w =
      expectation (principalPivotProductMass e F C w)
        (extractionIntegrand (C.coefficient M e a w) χ κ
          (fun col => principalDivisorWeight e F C col w)
          (maskSubsetIntegerForm (C.coefficient M e a w))) := by
  unfold principalWeightedColorCount extractionIntegrand principalBoundedCountIntegrand
    principalColorWeight extractionSumFactor principalColorProductMask extractionProductFactor
  congr 1
  funext z
  congr 3
  ext S
  simp

/-- Positive actual count gives an actual support tuple whose scaled
coordinates have every nonempty subset sum and product in one color. -/
theorem principal_positive_count_extract {n m r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r)
    (κ : Fin r) (w : ℕ)
    (hc : ∀ i, 0 < C.coefficient M e a w i)
    (hd : ∀ S : NonemptyColumnSubset (m+1), ∀ k ∈ S.val,
      C.coefficient M e a w (S.val.max' S.property) ∣ C.coefficient M e a w k)
    (hcount : 0 < principalWeightedColorCount C M e F a χ (fun _ => κ) κ w) :
    ∃ z ∈ (principalPivotProductMass e F C w).support,
      (∀ i, 0 < z i ∧ 0 < C.coefficient M e a w i * (z i).toNat) ∧
      ∀ S : Finset (Fin (m+1)), S.Nonempty →
        χ (∑ k ∈ S, C.coefficient M e a w k * (z k).toNat) = κ ∧
        χ (∏ k ∈ S, C.coefficient M e a w k * (z k).toNat) = κ := by
  rw [principalWeightedColorCount_extraction_eq] at hcount
  apply positive_color_count_extract (C.coefficient M e a w) χ κ
    (fun col => principalDivisorWeight e F C col w)
    (maskSubsetIntegerForm (C.coefficient M e a w))
    (principalPivotProductMass e F C w) hc ?_ hcount
  intro z _ S
  exact maskSubsetIntegerForm_scaled _ S (hd S) z

/-- Existing admissibility conditions supply all positivity and exact
integer-ratio hypotheses needed for extraction, uniformly at late stages. -/
theorem MasterParameterConditions.principal_positive_count_extract_eventually
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : PrincipalCoordinateChain n (m+1)) (a : Fin (m+1) → ℚ)
    (ha : ∀ i, a i ∈ A) (χ : ℕ → Fin r) :
    ∀ᶠ w in atTop, ∀ κ : Fin r,
      0 < principalWeightedColorCount C M e F a χ (fun _ => κ) κ w →
      ∃ z ∈ (principalPivotProductMass e F C w).support,
        (∀ i, 0 < z i ∧ 0 < C.coefficient M e a w i * (z i).toNat) ∧
        ∀ S : Finset (Fin (m+1)), S.Nonempty →
          χ (∑ k ∈ S, C.coefficient M e a w k * (z k).toNat) = κ ∧
          χ (∏ k ∈ S, C.coefficient M e a w k * (z k).toNat) = κ := by
  have hforms := hF.subset_scaled_forms a ha (fun _ => C.lift e)
    (fun _ => C.lift_range e heM)
  filter_upwards [hforms] with w hw
  intro κ hcount
  apply principal_positive_count_extract C M e F a χ κ w ?_ ?_ hcount
  · simpa only [C.coefficient_lift e heM] using hw.1
  · simpa only [C.coefficient_lift e heM] using (fun S => (hw.2 S).1)

end Hindman168
