import Hindman168.PrincipalBlockCalibration
import Hindman168.PrincipalBoundedCounts
import Hindman168.MaskColorFamilyChainReplacement

/-! The paper's unbounded weighted count uses the actual selected pivot
laws and independent tail-product divisor weights. Singleton center
weights and all nonempty product masks are retained exactly. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

noncomputable def principalDivisorWeight {n m : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (C : PrincipalCoordinateChain n m) (col : Fin m)
    (w : ℕ) (y : ℤ) : ℝ := integerDivisorMask (principalTailMass e F (C.tail col) w) y

noncomputable def principalPivotProductMass {n m : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (C : PrincipalCoordinateChain n m) (w : ℕ) : Mass (Fin m → ℤ) :=
  piMass (fun col => integerMass (F.cutoff w (energyPrincipal e (C.pivot col))) (primorial w))

noncomputable def principalColorWeight {n m r : ℕ} (C : PrincipalCoordinateChain n (m+1))
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r)
    (col : Fin (m+1)) (w : ℕ) (y : ℤ) : ℝ :=
  principalDivisorWeight e F C col w y *
    (if 0 < y then if χ (C.coefficient M e a w col * y.toNat) = color col then 1 else 0 else 0)

noncomputable def principalWeightedColorCount {n m r : ℕ} (C : PrincipalCoordinateChain n (m+1))
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r)
    (productColor : Fin r) (w : ℕ) : ℝ :=
  expectation (principalPivotProductMass e F C w) (fun z =>
    (∏ col, principalDivisorWeight e F C col w (z col)) *
    principalBoundedCountIntegrand C M e a w
      (fun col => principalColorWeight C M e F a χ color col w)
      (principalColorProductMask C M e a χ productColor w) z)

theorem principalDivisorWeight_lift {n m : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (C : PrincipalCoordinateChain n m) (col : Fin m)
    (w : ℕ) (y : ℤ) :
    principalDivisorWeight e F C col w y = integerDivisorMask
      (tailMass (primorial w) ((C.lift e).tailCutoffs (F.cutoff w) col)) y := by
  unfold principalDivisorWeight
  rw [principalTailMass_image]
  rfl

theorem principalPivotProductMass_lift {n m M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (C : PrincipalCoordinateChain n (m+1)) (gap : ℕ → Fin M) (w : ℕ) :
    principalPivotProductMass e (maskGeneratedMaster m gap) C w =
      maskOriginalBaseMass m gap (fun _ => C.lift e) w := rfl

theorem principalColorWeight_lift {n m M r : ℕ} (C : PrincipalCoordinateChain n (m+1))
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (hM : 0 < M) (gap : ℕ → Fin M)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r)
    (col : Fin (m+1)) (w : ℕ) (y : ℤ) :
    principalColorWeight C M e (maskGeneratedMaster m gap) a χ color col w y =
      maskChainColorWeight m hM (C.lift e) (C.lift_range e heM) a χ color col w y := by
  have hc := principalBlockCoefficient_lift e heM (C.tail col) (C.pivot col) (a col) w
  change C.coefficient M e a w col = _ at hc
  unfold principalColorWeight
  rw [principalDivisorWeight_lift, hc]
  rfl

theorem mask_principal_weighted_count_exact {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (hM : 0 < M) (gap : ℕ → Fin M)
    (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
    (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r) (productColor : Fin r) :
    ∀ᶠ w in atTop,
      maskOriginalSubsetCorrelation gap a (fun _ => C.lift e) w
        (maskCenterAndRows gap (fun _ => C.lift e) w
          (fun col => maskChainColorWeight m hM (C.lift e) (C.lift_range e heM) a χ color col w))
        (principalColorProductMask C M e a χ productColor w) =
      principalWeightedColorCount C M e (maskGeneratedMaster m gap) a χ color productColor w := by
  let A := Finset.univ.image a
  have hA : ∀ v ∈ A, 0 < v := by
    intro v hv
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hv
    exact ha col
  have hF := maskGeneratedMaster_conditions m gap A hA
  have hc := hF.column_coefficients a (fun col => Finset.mem_image.mpr ⟨col, by simp, rfl⟩)
    (fun _ => (C.lift e).block) (fun _ => C.lift_range e heM)
    (fun _ col => (C.lift e).block_nonempty col)
  filter_upwards [hc] with w hw
  rw [maskCenterAndRows_bounded_count gap a (fun _ => C.lift e) w (fun col => (hw col).1)]
  unfold principalWeightedColorCount
  rw [principalPivotProductMass_lift]
  have hr : (fun col => principalColorWeight C M e (maskGeneratedMaster m gap) a χ color col w) =
      (fun col => maskChainColorWeight m hM (C.lift e) (C.lift_range e heM) a χ color col w) := by
    funext col y
    exact principalColorWeight_lift C e heM hM gap a χ color col w y
  rw [hr]
  simp_rw [principalDivisorWeight_lift]
  rw [principalBoundedCountIntegrand_lift C e heM gap]

end Hindman168
