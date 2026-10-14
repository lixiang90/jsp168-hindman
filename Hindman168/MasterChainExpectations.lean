import Hindman168.MasterChainSampling

/-!
# Mass normalization and arbitrary bounded tests for actual master chains

The weighted comparison measure keeps its original mass. Its mass is
one plus a rapidly small error because the actual raw law has total one.
Polynomially bounded real, complex or normed-space tests transfer at all
inverse real-power scales, even when the tests and chain depend on w.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.chain_comparison_total_rapid {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ i, V w ≤ F.auxiliary w ((C w).pivot i)) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.total (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w)))) - 1) := by
  apply (hF.chain_joint_rapid C hN hV hbudget).of_abs_le
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have ht : FiniteMass.total ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
      (fun x => List.ofFn ((C w).sampleProducts (hN w) x))) = 1 := by
    rw [FiniteMass.total_push]
    exact FiniteMass.piMass_total_one (fun j : Fin N => rawMass (F.cutoff w j) (primorial w))
      (fun j => rawMass_total ((hw j.val (Finset.mem_range.mpr j.isLt)).2.2))
  have hb := FiniteMass.total_distance_le
    ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
      (fun x => List.ofFn ((C w).sampleProducts (hN w) x)))
    (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w))))
  rw [ht, abs_sub_comm] at hb
  exact hb.trans (le_abs_self _)

theorem MasterParameterConditions.chain_expectation_real_power {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ i, V w ≤ F.auxiliary w ((C w).pivot i))
    (B : ℕ) (f : ℕ → List ℕ → E)
    (hf : ∀ᶠ w in atTop, ∀ y, ‖f w y‖ ≤ (V w : ℝ) ^ B) (s : ℝ) :
    (fun w => FiniteMass.normedExpectation
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x))) (f w) -
      FiniteMass.normedExpectation
        (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w)))) (f w))
      =o[atTop] (fun w => (V w : ℝ) ^ (-s)) :=
  normed_expectation_transfer_isLittleO (hV.mono (fun _ hw => by omega))
    (hF.chain_joint_rapid C hN hV hbudget) (Eventually.of_forall (fun _ => le_rfl)) B f hf s

theorem constructedMasterFamily_chain_expectation_real_power {n N m : ℕ}
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (B : ℕ) (f : ℕ → List ℕ → E)
    (hf : ∀ᶠ w in atTop, ∀ y, ‖f w y‖ ≤ ((constructedMasterFamily N D hD).auxiliary w 0 : ℝ) ^ B)
    (s : ℝ) :
    let F := constructedMasterFamily N D hD
    (fun w => FiniteMass.normedExpectation
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x))) (f w) -
      FiniteMass.normedExpectation
        (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w)))) (f w))
      =o[atTop] (fun w => (F.auxiliary w 0 : ℝ) ^ (-s)) := by
  let F := constructedMasterFamily N D hD
  have hF := constructedMasterFamily_conditions N A hA D hD
  apply hF.chain_expectation_real_power C hN _ _ B f hf s
  · exact Eventually.of_forall (fun w => by
      change 1 ≤ F.auxiliary w 0
      have h := F.auxiliary_ge_two w 0
      omega)
  · exact Eventually.of_forall (fun w i => hF.auxiliary_monotone w (Nat.zero_le _))

end Hindman168
