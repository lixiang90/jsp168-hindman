import Hindman168.PrincipalCoordinateProducts
import Hindman168.MaskColorProductMasks

/-! The bounded count on the selected independent harmonic coordinates
has the same normalized forms and every nonempty product-color mask. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

noncomputable def principalBoundedCountIntegrand {n m : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (a : Fin (m+1) → ℚ) (w : ℕ) (S : Fin (m+1) → ℤ → ℝ)
    (b : Finset (Fin (m+1)) → ℤ → ℝ) (z : Fin (m+1) → ℤ) : ℝ :=
  (∏ V : NonemptyColumnSubset (m+1), if 2 ≤ V.val.card then
    S (V.val.max' V.property) (maskSubsetIntegerForm (C.coefficient M e a w) V z) else 1) *
    ∏ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, b V (∏ k ∈ V, z k)

noncomputable def principalColorProductMask {n m r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (y : ℤ) : ℝ :=
  if 0 < y ∧ χ ((∏ k ∈ V, C.coefficient M e a w k) * y.toNat) = color then 1 else 0

theorem principalBoundedCountIntegrand_lift {n m M : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (gap : ℕ → Fin M) (a : Fin (m+1) → ℚ) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ) :
    principalBoundedCountIntegrand C M e a w S b =
      maskBoundedCountIntegrand gap a (fun _ => C.lift e) w S b := by
  funext z
  unfold principalBoundedCountIntegrand maskBoundedCountIntegrand
  rw [C.coefficient_lift e heM]

theorem principalColorProductMask_lift {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (a : Fin (m+1) → ℚ)
    (χ : ℕ → Fin r) (color : Fin r) (w : ℕ) :
    principalColorProductMask C M e a χ color w =
      maskColorProductMask (N := M) a (fun _ => C.lift e) χ color w := by
  funext V y
  unfold principalColorProductMask maskColorProductMask
  rw [C.coefficient_lift e heM]

theorem MasterParameterConditions.principal_bounded_count_expectation {d n m M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (C : PrincipalCoordinateChain n (m+1))
    (gap : ℕ → Fin M) (a : Fin (m+1) → ℚ) :
    ∀ᶠ w in atTop, ∀ (S : Fin (m+1) → ℤ → ℝ)
      (b : Finset (Fin (m+1)) → ℤ → ℝ),
      expectation (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => maskBoundedCountIntegrand gap a (fun _ => C.lift e) w S b
          (fun col => ((C.lift e).sampleProducts (C.lift_range e heM) x col : ℤ))) =
      expectation (selectedPrincipalRawMass e F w)
        (fun x => principalBoundedCountIntegrand C M e a w S b
          (fun col => (C.sampleProducts x col : ℤ))) := by
  filter_upwards [hF.principal_chain_expectation e heM C] with w hw
  intro S b
  rw [principalBoundedCountIntegrand_lift C e heM gap]
  exact hw (fun z => maskBoundedCountIntegrand gap a (fun _ => C.lift e) w S b
    (fun col => (z col : ℤ)))

theorem principalColorProductMask_natural {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (a : Fin (m+1) → ℚ)
    (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (z : Fin (m+1) → ℕ) (hz : ∀ k ∈ V, 0 < z k) :
    principalColorProductMask C M e a χ color w V ((∏ k ∈ V, z k : ℕ) : ℤ) =
      if χ (∏ k ∈ V, C.coefficient M e a w k * z k) = color then 1 else 0 := by
  rw [principalColorProductMask_lift C e heM, C.coefficient_lift e heM]
  exact maskColorProductMask_natural a (fun _ => C.lift e) χ color w V z hz

end Hindman168
