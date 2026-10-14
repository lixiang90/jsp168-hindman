import Hindman168.FiniteMasterSelection

/-!
# Uniform actual master-chain product sampling

The chain itself may vary with w inside the fixed master index set.
Its actual independent raw-coordinate product law is approximated by
the weighted pivot product law at every inverse-power scale permitted
by all selected pivot budgets. The constructed family admits the common
base V_0 without any extra growth or normalization hypotheses.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

def Chain.pivotIndex {m N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (i : Fin m) : Fin N :=
  ⟨C.pivot i, Finset.mem_range.mp (hN i (Finset.mem_insert_self _ _))⟩

theorem MasterParameterConditions.chain_sampling_growth {n N m : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, ∀ i, V w ≤ F.auxiliary w ((C w).pivot i)) (i : Fin m) :
    PowerDominates atTop (fun w => Real.log ((C w).cutoffs (F.cutoff w) i).pivotCutoff)
      (fun w => (samplingSize (primorial w)
        (tailBound ((C w).cutoffs (F.cutoff w) i).tailCutoffs) 0 (V w) : ℝ)) := by
  exact hF.indexed_sampling_budget_growth (fun w => (C w).pivotIndex (hN w) i)
    (Eventually.of_forall (fun w => hF.chain_tail_budget (C w) w i))
    (Eventually.of_forall (fun _ => Nat.zero_le _)) (hV.mono (fun _ hw => hw i))

theorem MasterParameterConditions.chain_joint_rapid {n N m : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ i, V w ≤ F.auxiliary w ((C w).pivot i)) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w => FiniteMass.distance
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x)))
      (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w))))) := by
  have ht : ∀ᶠ w in atTop, ∀ i,
      ValidCutoffs ((C w).cutoffs (F.cutoff w) i).tailCutoffs (primorial w) := by
    filter_upwards [hF.raw_cutoffs_valid] with w hw i
    exact chain_tailCutoffs_valid (C w) (F.cutoff w) (primorial w) (hN w)
      (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) i
  have hg (i : Fin m) := hF.chain_sampling_growth C hN hbudget i
  have hp := joint_product_law_rapid hg hV (Eventually.of_forall primorial_pos) ht
  apply hp.of_abs_le
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  rw [global_chain_joint_mass (C w) (F.cutoff w) (primorial w) (hN w)
    (fun j => (hw j.val (Finset.mem_range.mpr j.isLt)).2.2)]

theorem MasterParameterConditions.chain_integer_joint_rapid {n N m : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ i, V w ≤ F.auxiliary w ((C w).pivot i)) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w => FiniteMass.distance
      (((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x))).mapDomain
          (fun xs : List ℕ => xs.map (fun a : ℕ => (a : ℤ))))
      (jointIntegerComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w))))) := by
  simpa only [jointIntegerComparison,
    FiniteMass.distance_push_injective (f := fun xs : List ℕ => xs.map (fun a : ℕ => (a : ℤ)))
      list_natCast_injective] using hF.chain_joint_rapid C hN hV hbudget

theorem constructedMasterFamily_chain_joint_rapid {n N m : ℕ} (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) :
    let F := constructedMasterFamily N D hD
    RapidlySmall atTop (fun w => (F.auxiliary w 0 : ℝ)) (fun w => FiniteMass.distance
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x)))
      (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w))))) := by
  let F := constructedMasterFamily N D hD
  have hF := constructedMasterFamily_conditions N A hA D hD
  apply hF.chain_joint_rapid C hN
  · exact Eventually.of_forall (fun w => by
      change 1 ≤ F.auxiliary w 0
      have h := F.auxiliary_ge_two w 0
      omega)
  · exact Eventually.of_forall (fun w i => hF.auxiliary_monotone w (Nat.zero_le _))

theorem constructedMasterFamily_chain_joint_real_power {n N m : ℕ} (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (s : ℝ) :
    let F := constructedMasterFamily N D hD
    (fun w => FiniteMass.distance
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x)))
      (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w)))))
      =o[atTop] (fun w => (F.auxiliary w 0 : ℝ) ^ (-s)) := by
  apply (constructedMasterFamily_chain_joint_rapid A hA D hD C hN).rpow_scale
  exact Eventually.of_forall (fun w => by
    have h := (constructedMasterFamily N D hD).auxiliary_ge_two w 0
    exact_mod_cast (by omega : 1 ≤ (constructedMasterFamily N D hD).auxiliary w 0))

end Hindman168
