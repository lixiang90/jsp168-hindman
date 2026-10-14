import Hindman168.MasterCopiedReplicaCubeMeanOne
import Hindman168.PredictionCopiedCancellation

/-!
# Actual master terminal cancellation for duplicated prediction cube rows

All signed subset moments are derived from the actual copied-row master
mean-one theorem. Multiple root copies and retained one-plus weights are
allowed. The common original prime-only event probability cancels exactly,
without a supplied copied-row independence or moment convergence premise.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterCopiedPredictionCubeWeight {m q r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin q → Fin m)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir) (w : ℕ) (u : Fin q)
    (x : Fin r → ℕ) (y : Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) (label w u)))
    (∑ j, masterCopiedPredictionCubeCoefficient s f dir row w x u j * y j)

theorem masterCopiedPredictionCubeWeight_subset_average_eq {m q r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → ℕ)
    (base : ℕ → (Fin r → ℕ) → Mass (Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ))
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir) (E : ℕ → (Fin r → ℕ) → Prop)
    (S : Finset (Fin q)) (w : ℕ) :
    conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w)) (base w) (E w)
      (fun x y => ∏ u ∈ S, masterCopiedPredictionCubeWeight F C label s f dir row w u x y) =
    masterChainWeightedMean F w (C w)
      (fun u => label w ((Fintype.equivFin S).symm u).val) (gap w) (base w)
      (masterCopiedPredictionCubeCoefficient s f dir (fun w u => row w ((Fintype.equivFin S).symm u).val) w)
      (E w) := by
  unfold conditionalFiniteAverage masterChainWeightedMean
  congr 1
  funext x
  split_ifs
  · congr 1
    funext y
    exact (finset_product_fin_equiv S
      (fun u => masterCopiedPredictionCubeWeight F C label s f dir row w u x y)).symm
  · rfl

theorem MasterParameterConditions.copied_replica_cube_centered_majorant_tendsto
    {n N m q r b d h L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (Γ U : Finset (Fin q)) (hdisjoint : Disjoint Γ U) (hΓ : Γ.Nonempty) :
    Tendsto (fun w => conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => (∏ u ∈ Γ, (masterCopiedPredictionCubeWeight F C label s f dir row w u x y - 1)) *
        ∏ u ∈ U, (1 + masterCopiedPredictionCubeWeight F C label s f dir row w u x y)))
      atTop (𝓝 0) := by
  apply centered_majorant_average_tendsto_zero
    (fun w => masterPrimeSlotsMass F w (fun j => gap w j))
    (masterMixedBaseMass H F index loc len) E
    (masterCopiedPredictionCubeWeight F C label s f dir row) Γ U hdisjoint hΓ
    (fun w => event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
  intro S _
  simp_rw [masterCopiedPredictionCubeWeight_subset_average_eq F C label
    (fun w j => (gap w j : ℕ)) (masterMixedBaseMass H F index loc len) s f dir row E S]
  apply hF.copied_replica_cube_mean_one_tendsto C hN
    (fun w u => label w ((Fintype.equivFin S).symm u).val) gap V hV
    (hdivbudget.mono (fun _ hw u => hw ((Fintype.equivFin S).symm u).val))
    hprimebudget T hT s e hs f hf dir
    (fun w u => row w ((Fintype.equivFin S).symm u).val)
    ?_ H index Tmin loc len E hharmbudget hlengthgrowth hlen
  exact hrow.mono (fun w hr => hr.comp
    (Subtype.val_injective.comp (Fintype.equivFin S).symm.injective))

theorem MasterParameterConditions.copied_replica_cube_majorant_mean_tendsto
    {n N m q r b d h L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => ∏ u ∈ U, (1 + masterCopiedPredictionCubeWeight F C label s f dir row w u x y)) -
      ((2 ^ U.card : ℕ) : ℝ) * event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
      atTop (𝓝 0) := by
  apply retained_majorant_average_mean_one
    (fun w => masterPrimeSlotsMass F w (fun j => gap w j))
    (masterMixedBaseMass H F index loc len) E
    (masterCopiedPredictionCubeWeight F C label s f dir row) U
    (fun w => event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
  intro S _
  simp_rw [masterCopiedPredictionCubeWeight_subset_average_eq F C label
    (fun w j => (gap w j : ℕ)) (masterMixedBaseMass H F index loc len) s f dir row E S]
  apply hF.copied_replica_cube_mean_one_tendsto C hN
    (fun w u => label w ((Fintype.equivFin S).symm u).val) gap V hV
    (hdivbudget.mono (fun _ hw u => hw ((Fintype.equivFin S).symm u).val))
    hprimebudget T hT s e hs f hf dir
    (fun w u => row w ((Fintype.equivFin S).symm u).val)
    ?_ H index Tmin loc len E hharmbudget hlengthgrowth hlen
  exact hrow.mono (fun w hr => hr.comp
    (Subtype.val_injective.comp (Fintype.equivFin S).symm.injective))

theorem MasterParameterConditions.copied_replica_cube_majorant_eventually_le
    {n N m q r b d h L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (U : Finset (Fin q)) :
    ∀ᶠ w in atTop, conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => ∏ u ∈ U, (1 + masterCopiedPredictionCubeWeight F C label s f dir row w u x y)) ≤
      ((2 ^ U.card : ℕ) : ℝ) + 1 := by
  apply varying_event_mean_eventually_le
    (k := fun w => event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
    ((2 ^ U.card : ℕ) : ℝ) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro w
    exact (event_le_total (masterPrimeSlotsMass F w (fun j => gap w j)) (E w)
      (hF.prime_slots_nonneg w (fun j => gap w j))).trans_eq
      (hF.prime_slots_total w (fun j => gap w j))
  · exact hF.copied_replica_cube_majorant_mean_tendsto C hN label gap V hV
      hdivbudget hprimebudget T hT s e hs f hf dir row hrow
      H index Tmin loc len E hharmbudget hlengthgrowth hlen U

end Hindman168
