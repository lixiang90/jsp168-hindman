import Hindman168.VariableHarmonicRows
import Hindman168.DivisorMaskExpansion
import Hindman168.FiniteWeightedErrors
import Hindman168.GlobalChainLaw

/-!
# Fresh independent raw draws for every divisor-mask occurrence

The coordinate index tags each raw draw with its row occurrence. Cutoff
or block labels may repeat, but no coordinate is shared across occurrences.
Grouping and product pushforward give the exact actual variable-row law.
List and chain-tail identifications connect this law to the original
divisor weights used by the master-family block comparison.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def freshDivisorRawMass {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (X : ∀ i, κ i → ℕ) (W : ℕ) : Mass ((Σ i, κ i) → ℕ) :=
  piMass (fun j => rawMass (X j.1 j.2) W)

def freshDivisorProducts {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (x : (Σ i, κ i) → ℕ) : Fin q → ℕ := fun i => ∏ j, x ⟨i,j⟩

theorem freshDivisorRawMass_nonneg {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (X : ∀ i, κ i → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W)
    (x : (Σ i, κ i) → ℕ) : 0 ≤ freshDivisorRawMass X W x :=
  piMass_nonneg _ (fun j n => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hH j.1 j.2) n) x

theorem freshDivisorRawMass_total {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (X : ∀ i, κ i → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    total (freshDivisorRawMass X W) = 1 :=
  piMass_total_one _ (fun j => rawMass_total (hH j.1 j.2))

theorem fresh_divisor_occurrences_joint_mass {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ) :
    (freshDivisorRawMass X W).mapDomain freshDivisorProducts = variableHarmonicRowDivisorMass X W := by
  have h := congrArg (fun μ : Mass (∀ i, κ i → ℕ) => μ.mapDomain (fun x i => ∏ j, x i j))
    (piMass_group (fun j : Σ i, κ i => rawMass (X j.1 j.2) W))
  rw [← Finsupp.mapDomain_comp, piMass_map] at h
  exact h

theorem fresh_divisor_occurrences_joint_pmf {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    (toPMF (freshDivisorRawMass X W) (freshDivisorRawMass_nonneg X W hH)
      (freshDivisorRawMass_total X W hH)).map freshDivisorProducts = variableHarmonicRowDivisorPMF X W hH := by
  rw [toPMF_map, variableHarmonicRowDivisorPMF_eq_toPMF]
  congr 1
  exact fresh_divisor_occurrences_joint_mass X W

theorem fresh_divisor_mask_expansion {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ) (z : Fin q → ℤ) :
    (∏ i, integerDivisorMask (harmonicDivisorMass (X i) W) (z i)) =
      expectation (freshDivisorRawMass X W) (fun x =>
        ((∏ i, freshDivisorProducts x i : ℕ) : ℝ) *
          (if ∀ i, (freshDivisorProducts x i : ℤ) ∣ z i then 1 else 0)) := by
  have hj := fresh_divisor_occurrences_joint_mass X W
  change (freshDivisorRawMass X W).mapDomain freshDivisorProducts =
    piMass (fun i => harmonicDivisorMass (X i) W) at hj
  rw [integerDivisorMask_product, ← hj, expectation_push]
  apply expectation_congr_support
  intro x hx
  split_ifs <;> rfl

theorem harmonicDivisorMass_list (Xs : List ℕ) (W : ℕ) :
    harmonicDivisorMass Xs.get W = tailMass W Xs := by
  rw [harmonicDivisorMass, piMass_raw_product, List.ofFn_get]

theorem harmonicDivisorMass_chain_tail {m : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ) (i : Fin m) :
    harmonicDivisorMass (fun j : C.tail i => X j) W = tailMass W (C.tailCutoffs X i) := by
  rw [harmonicDivisorMass]
  exact piMass_raw_product_equiv ((C.tail i).orderIsoOfFin rfl).toEquiv W _

theorem fresh_chain_tail_occurrences_joint_mass {m q : ℕ} (C : Chain m) (X : ℕ → ℕ)
    (W : ℕ) (label : Fin q → Fin m) :
    (freshDivisorRawMass (fun (i : Fin q) (j : C.tail (label i)) => X j) W).mapDomain
      freshDivisorProducts = piMass (fun i => tailMass W (C.tailCutoffs X (label i))) := by
  rw [fresh_divisor_occurrences_joint_mass, variableHarmonicRowDivisorMass]
  simp only [harmonicDivisorMass_chain_tail]

end Hindman168
