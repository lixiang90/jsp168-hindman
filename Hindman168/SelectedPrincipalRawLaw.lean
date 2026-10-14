import Hindman168.SelectedChainIndices
import Hindman168.MasterSamplingBudgets
import Hindman168.GlobalChainLaw
import Hindman168.UnitCRTJointLaw

/-! Discarding unused master coordinates gives exactly the independent
raw harmonic laws at the selected principal indices. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

def selectedPrincipalIndex {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (k : Fin n) : Fin M :=
  ⟨energyPrincipal e k, heM _⟩

theorem selectedPrincipalIndex_injective {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) : Function.Injective (selectedPrincipalIndex e heM) := by
  intro i j hij
  exact (energyPrincipal_strictMono e).injective (congrArg Fin.val hij)

noncomputable def selectedPrincipalRawMass {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (w : ℕ) : Mass (Fin n → ℕ) :=
  piMass (fun k => rawMass (F.cutoff w (energyPrincipal e k)) (primorial w))

theorem MasterParameterConditions.selected_principal_raw_law {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) :
    ∀ᶠ w in atTop,
      (globalRawMass (F.cutoff w) (primorial w) M).mapDomain
        (fun x k => x (selectedPrincipalIndex e heM k)) = selectedPrincipalRawMass e F w := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  exact piMass_restrict (fun j : Fin M => rawMass (F.cutoff w j) (primorial w))
    (selectedPrincipalIndex e heM) (selectedPrincipalIndex_injective e heM)
    (fun j => rawMass_total (hw j (Finset.mem_range.mpr j.isLt)).2.2)

theorem MasterParameterConditions.selected_principal_raw_expectation {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) :
    ∀ᶠ w in atTop, ∀ f : (Fin n → ℕ) → ℝ,
      expectation (globalRawMass (F.cutoff w) (primorial w) M)
          (fun x => f (fun k => x (selectedPrincipalIndex e heM k))) =
        expectation (selectedPrincipalRawMass e F w) f := by
  filter_upwards [hF.selected_principal_raw_law e heM] with w hw
  intro f
  have h := congrArg (fun μ : Mass (Fin n → ℕ) => expectation μ f) hw
  rw [expectation_push] at h
  exact h

theorem MasterParameterConditions.selected_principal_raw_probability {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) :
    ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1 := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have hz (k : Fin n) : 0 < harmonicNormalizer (F.cutoff w (energyPrincipal e k)) (primorial w) :=
    (hw _ (Finset.mem_range.mpr (heM _))).2.2
  refine ⟨piMass_nonneg _ (fun k y => ?_), piMass_total_one _ (fun k => rawMass_total (hz k))⟩
  rw [rawMass_apply]
  exact harmonicWeight_nonneg (hz k) y

end Hindman168
