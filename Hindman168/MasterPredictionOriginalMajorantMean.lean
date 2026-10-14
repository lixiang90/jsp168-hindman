import Hindman168.PredictionOriginalMixedLaw
import Hindman168.MasterCommonTailPrediction
import Hindman168.MasterPredictionOriginalCubeLimit

/-!
# One-plus cube means under the paper's original sampling laws

The common-tail budget derives the actual prime, harmonic and shift
budgets. Exact coordinate reindexing transports the already proved
subset mean theorem to the original harmonic root and independent shifts.
No subset-moment or majorant-mean convergence is assumed.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionOriginalMajorantAverage {N m r b d : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m)
    (root : ℕ → Fin N) (primeGap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (w : ℕ) : ℝ :=
  conditionalFiniteAverage (masterPrimeSlotsMass F w (primeGap w))
    (fun x => piMass (predictionOriginalColumnMass (F.cutoff w (root w).val)
      (primorial w) (A w x) (T w x))) (E w)
    (fun x z => ∏ row : ReplicaCubeRow b d,
      (1 + integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs (F.cutoff w) (label w row)))
        (replicaCubeEval (fun q => predictionCubeModulus w (s w q) (f q) x) row z)))

theorem MasterParameterConditions.prediction_original_majorant_mean_tendsto
    {n N m r b d L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, ∀ row, (C w).tail (label w row) ⊆ tail w)
    (root : ℕ → Fin N) (replicaGap : ℕ → Fin b → Fin N)
    (primeGap : ℕ → Fin r → Fin L) (k : Fin b → ℕ)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailreplica : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (replicaGap w q).val)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (primeGap w j))
    (polys : Finset (MvPolynomial (Fin r) ℤ)) (hpolys : ∀ p ∈ polys, p ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ q, f q ∈ polys)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (replicaGap w q).val (k q) ≤ T w x q) :
    Tendsto (fun w => masterPredictionOriginalMajorantAverage F C label root
      (fun w j => primeGap w j) s f A T E w -
      (2 : ℝ) ^ Fintype.card (ReplicaCubeRow b d) *
        event (masterPrimeSlotsMass F w (fun j => primeGap w j)) (E w)) atTop (𝓝 0) := by
  let V w := masterCommonTailBudget F w (tail w)
  let Tmin w q := masterShiftLengthLowerBound F w (replicaGap w q).val (k q)
  let H := predictionOriginalRootColumns b d
  let index w (_ : Fin (Fintype.card (ReplicaCubeColumn b d))) := root w
  let loc w x := predictionOriginalLocationFin (A w x)
  let len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ :=
    fun w x => predictionOriginalLengthFin (T w x)
  let lower : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ :=
    fun w => predictionOriginalLengthFin (Tmin w)
  let E' w x := E w x ∧ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support
  let row : ℕ → Fin (Fintype.card (ReplicaCubeRow b d)) → ReplicaCubeRow b d :=
    fun _w => (Fintype.equivFin (ReplicaCubeRow b d)).symm
  let lab w u := label w (row w u)
  have hV : ∀ᶠ w in atTop, 1 ≤ V w := Eventually.of_forall
    (fun w => (Nat.le_trans (by decide : 1 ≤ 2) (masterCommonTailBudget_ge_two F w (tail w))))
  have hVr : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (root w).val :=
    htailroot.mono (fun w hw => hF.common_tail_budget_le_auxiliary w _ _ hw)
  have hVq : ∀ᶠ w in atTop, ∀ q, V w ≤ F.auxiliary w (replicaGap w q).val :=
    htailreplica.mono (fun w hw q => hF.common_tail_budget_le_auxiliary w _ _ (hw q))
  have hVp : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (primeGap w j) :=
    htailprime.mono (fun w hw j => hF.common_tail_budget_le_auxiliary w _ _ (hw j))
  have hdiv : ∀ᶠ w in atTop, ∀ u,
      tailBound ((C w).tailCutoffs (F.cutoff w) (lab w u)) ≤ V w :=
    htail.mono (fun w hw u => hF.common_tail_divisor_budget (C w) w _ _ (hw (row w u)))
  have hg (q : Fin b) : PowerDominates atTop (fun w => (Tmin w q : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) := by
    apply (hF.quotient_sqrt_sampling_growth (fun w => replicaGap w q) (k q)
      (hVq.mono (fun _ hw => hw q))).mono_right
    exact Eventually.of_forall (fun _ => ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.sqrt_le_self _⟩)
  have hgFin (j : Fin (Fintype.card (ReplicaCubeColumn b d))) (hj : j ∉ H) :
      PowerDominates atTop (fun w => (lower w j : ℝ))
        (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) := by
    have hn : (Fintype.equivFin (ReplicaCubeColumn b d)).symm j ≠ none :=
      fun h => hj (predictionOriginalRootColumns_mem j |>.mpr h)
    cases hc : (Fintype.equivFin (ReplicaCubeColumn b d)).symm j with
    | none => exact False.elim (hn hc)
    | some c => simpa only [lower, predictionOriginalLengthFin, hc] using hg c.1
  have hlen : ∀ᶠ w in atTop, ∀ x, E' w x → ∀ j, j ∉ H → lower w j ≤ len w x j := by
    filter_upwards [hT] with w hw
    intro x hx j hj
    have hn : (Fintype.equivFin (ReplicaCubeColumn b d)).symm j ≠ none :=
      fun h => hj (predictionOriginalRootColumns_mem j |>.mpr h)
    cases hc : (Fintype.equivFin (ReplicaCubeColumn b d)).symm j with
    | none => exact False.elim (hn hc)
    | some c => simpa only [lower, len, predictionOriginalLengthFin, hc] using hw x hx.2 hx.1 c.1
  have hharm : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val :=
    hVr.mono (fun _ hw _ _ => hw)
  have hm := hF.replica_cube_majorant_mean_tendsto C hN lab primeGap V hV hdiv hVp
    polys hpolys s e hs f hf row (Eventually.of_forall (fun _ => (Fintype.equivFin _).symm.injective))
    H index lower loc len E' hharm hgFin hlen Finset.univ
  have he (w : ℕ) : conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => primeGap w j))
      (masterMixedBaseMass H F index loc len w) (E' w)
      (fun x y => ∏ u : Fin (Fintype.card (ReplicaCubeRow b d)),
        (1 + masterPredictionCubeWeight F C lab s f row w u x y)) =
      masterPredictionOriginalMajorantAverage F C label root (fun w j => primeGap w j) s f A T E w := by
    rw [conditionalFiniteAverage_support_event]
    unfold conditionalFiniteAverage masterPredictionOriginalMajorantAverage
    apply congrArg (expectation (masterPrimeSlotsMass F w (fun j => primeGap w j)))
    funext x
    split_ifs
    · change expectation (mixedIntegerBaseMass H (fun _ => F.cutoff w (root w).val)
        (primorial w) (loc w x) (len w x)) _ = _
      rw [prediction_original_mixed_expectation]
      apply congrArg (expectation (piMass (predictionOriginalColumnMass
        (F.cutoff w (root w).val) (primorial w) (A w x) (T w x))))
      funext z
      have hev (u : Fin (Fintype.card (ReplicaCubeRow b d))) :
          masterPredictionCubeWeight F C lab s f row w u x
            (fun j => z ((Fintype.equivFin (ReplicaCubeColumn b d)).symm j)) =
          integerDivisorMask (tailMass (primorial w)
            ((C w).tailCutoffs (F.cutoff w) (label w (row w u))))
            (replicaCubeEval (fun q => predictionCubeModulus w (s w q) (f q) x) (row w u) z) := by
        unfold masterPredictionCubeWeight masterPredictionCubeCoefficient
        rw [replicaCubeFinCoefficient_eval]
      simp_rw [hev]
      exact Fintype.prod_equiv (Fintype.equivFin (ReplicaCubeRow b d)).symm _ _ (fun _ => rfl)
    · rfl
  have hprob (w : ℕ) : event (masterPrimeSlotsMass F w (fun j => primeGap w j)) (E' w) =
      event (masterPrimeSlotsMass F w (fun j => primeGap w j)) (E w) := by
    rw [← expectation_indicator, ← expectation_indicator]
    apply expectation_congr_support
    intro x hx
    simp only [E', hx, and_true]
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, he, hprob] using hm

end Hindman168
