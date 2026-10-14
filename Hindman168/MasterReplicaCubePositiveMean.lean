import Hindman168.MasterReplicaCubeMajorant
import Hindman168.MasterReplicaCubeMeanOne
import Hindman168.PredictionCopiedCancellation

/-!
# Uncopied replica majorant means under the actual master law

Each subset mean is derived from the concrete integer cube rows. This
retains the original prime-only event mass and includes the root one-plus
factor required by the dual moment argument.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.replica_cube_majorant_mean_tendsto
    {n N m q r b d L : ℕ}
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
    (row : ℕ → Fin q → ReplicaCubeRow b d)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (ReplicaCubeColumn b d))))
    (index : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => ∏ u ∈ U, (1 + masterPredictionCubeWeight F C label s f row w u x y)) -
      ((2 ^ U.card : ℕ) : ℝ) * event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
      atTop (𝓝 0) := by
  apply retained_majorant_average_mean_one
    (fun w => masterPrimeSlotsMass F w (fun j => gap w j))
    (masterMixedBaseMass H F index loc len) E
    (masterPredictionCubeWeight F C label s f row) U
    (fun w => event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
  intro S _
  simp_rw [masterPredictionCubeWeight_subset_average_eq F C label
    (fun w j => (gap w j : ℕ)) (masterMixedBaseMass H F index loc len) s f row E S]
  apply hF.replica_cube_mean_one_tendsto C hN
    (fun w u => label w ((Fintype.equivFin S).symm u).val) gap V hV
    (hdivbudget.mono (fun _ hw u => hw ((Fintype.equivFin S).symm u).val))
    hprimebudget T hT s e hs f hf
    (fun w u => row w ((Fintype.equivFin S).symm u).val)
    ?_ H index Tmin loc len E hharmbudget hlengthgrowth hlen
  exact hrow.mono (fun w hr => hr.comp
    (Subtype.val_injective.comp (Fintype.equivFin S).symm.injective))

theorem MasterParameterConditions.replica_cube_majorant_eventually_le
    {n N m q r b d L : ℕ}
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
    (row : ℕ → Fin q → ReplicaCubeRow b d)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (ReplicaCubeColumn b d))))
    (index : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (U : Finset (Fin q)) :
    ∀ᶠ w in atTop, conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => ∏ u ∈ U, (1 + masterPredictionCubeWeight F C label s f row w u x y)) ≤
      ((2 ^ U.card : ℕ) : ℝ) + 1 := by
  apply varying_event_mean_eventually_le
    (k := fun w => event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
    ((2 ^ U.card : ℕ) : ℝ) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro w
    exact (event_le_total (masterPrimeSlotsMass F w (fun j => gap w j)) (E w)
      (hF.prime_slots_nonneg w (fun j => gap w j))).trans_eq
      (hF.prime_slots_total w (fun j => gap w j))
  · exact hF.replica_cube_majorant_mean_tendsto C hN label gap V hV
      hdivbudget hprimebudget T hT s e hs f hf row hrow
      H index Tmin loc len E hharmbudget hlengthgrowth hlen U

end Hindman168
