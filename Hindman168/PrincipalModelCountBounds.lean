import Hindman168.PrincipalPredictionModels
import Hindman168.FiniteProbabilityBounds

/-! The selected calibration probabilities and complete bounded model
counts lie in [0,1] under the actual eventually normalized raw laws. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

noncomputable def principalCalibrationProbability {n r : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily) (T : Finset (Fin n)) (b : Fin n)
    (a : ℚ) (χ : ℕ → Fin r) (color : Fin r) (S : ℕ → ℤ → ℝ) (θ : ℝ) (w : ℕ) : ℝ :=
  event (selectedPrincipalRawMass e F w)
    (fun x => let z : ℤ := (principalSubsetProduct (insert b T) x : ℤ)
      0 < z ∧ χ (principalBlockCoefficient M e T b a w * z.toNat) = color ∧ S w z ≤ 2*θ)

noncomputable def principalModelColorCount {n m r : ℕ} (C : PrincipalCoordinateChain n (m+1))
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (productColor : Fin r)
    (S : Fin (m+1) → ℕ → ℤ → ℝ) (w : ℕ) : ℝ :=
  expectation (selectedPrincipalRawMass e F w)
    (fun x => principalBoundedCountIntegrand C M e a w (fun col => S col w)
      (principalColorProductMask C M e a χ productColor w)
      (fun col => (C.sampleProducts x col : ℤ)))

theorem principalColorProductMask_Icc {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (y : ℤ) :
    principalColorProductMask C M e a χ color w V y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold principalColorProductMask
  split_ifs <;> norm_num

theorem principalBoundedColorIntegrand_Icc {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (hS : ∀ col y, S col y ∈ Set.Icc (0 : ℝ) 1)
    (z : Fin (m+1) → ℤ) :
    principalBoundedCountIntegrand C M e a w S
      (principalColorProductMask C M e a χ color w) z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold principalBoundedCountIntegrand
  have hrow (V : NonemptyColumnSubset (m+1)) :
      (if 2 ≤ V.val.card then S (V.val.max' V.property)
        (maskSubsetIntegerForm (C.coefficient M e a w) V z) else 1) ∈ Set.Icc (0 : ℝ) 1 := by
    split_ifs
    · exact hS _ _
    · norm_num
  have hr0 := Finset.prod_nonneg (fun V (_ : V ∈ (Finset.univ : Finset (NonemptyColumnSubset (m+1)))) => (hrow V).1)
  have hr1 := Finset.prod_le_one (fun V (_ : V ∈ (Finset.univ : Finset (NonemptyColumnSubset (m+1)))) => (hrow V).1)
    (fun V _ => (hrow V).2)
  have hm0 := Finset.prod_nonneg (s := (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅)
    (fun V _ => (principalColorProductMask_Icc (M := M) C e a χ color w V (∏ k ∈ V, z k)).1)
  have hm1 := Finset.prod_le_one (s := (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅)
    (fun V _ => (principalColorProductMask_Icc (M := M) C e a χ color w V (∏ k ∈ V, z k)).1)
    (fun V _ => (principalColorProductMask_Icc (M := M) C e a χ color w V (∏ k ∈ V, z k)).2)
  exact ⟨mul_nonneg hr0 hm0, (mul_le_mul hr1 hm1 hm0 zero_le_one).trans_eq (by norm_num)⟩

theorem principalCalibrationProbability_Icc {n r : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (T : Finset (Fin n)) (b : Fin n) (a : ℚ) (χ : ℕ → Fin r) (color : Fin r)
    (S : ℕ → ℤ → ℝ) (θ : ℝ) :
    ∀ᶠ w in atTop, principalCalibrationProbability M e F T b a χ color S θ w ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [hprob] with w hw
  exact event_probability_Icc _ hw.1 hw.2 _

theorem principalModelColorCount_Icc {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin r)
    (S : Fin (m+1) → ℕ → ℤ → ℝ) (hS : ∀ col w y, S col w y ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ w in atTop, principalModelColorCount C M e F a χ color S w ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [hprob] with w hw
  exact expectation_probability_Icc _ hw.1 hw.2 _
    (fun x => principalBoundedColorIntegrand_Icc C e a χ color w _ (fun col y => hS col w y) _)

end Hindman168
