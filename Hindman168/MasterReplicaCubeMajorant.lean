import Hindman168.PredictionMajorantCancellation

/-!
# Root-centered replica cube majorants under the actual master laws

Each subset moment is proved with the concrete replica coefficients and
original divisor and mixed base laws. Expanding the retained majorants
then cancels the common event mass. This proves the initial cube prefactor
limit; it does not yet implement the later repeated Cauchy--Schwarz copies.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionCubeWeight {m q r b d : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin q → Fin m)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (row : ℕ → Fin q → ReplicaCubeRow b d) (w : ℕ) (u : Fin q)
    (x : Fin r → ℕ) (y : Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) (label w u)))
    (∑ j, masterPredictionCubeCoefficient s f row w x u j * y j)

theorem masterPredictionCubeWeight_subset_average_eq {m q r b d : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → ℕ)
    (base : ℕ → (Fin r → ℕ) → Mass (Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ))
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (row : ℕ → Fin q → ReplicaCubeRow b d) (E : ℕ → (Fin r → ℕ) → Prop)
    (S : Finset (Fin q)) (w : ℕ) :
    conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w)) (base w) (E w)
      (fun x y => ∏ u ∈ S, masterPredictionCubeWeight F C label s f row w u x y) =
    masterChainWeightedMean F w (C w)
      (fun u => label w ((Fintype.equivFin S).symm u).val) (gap w) (base w)
      (masterPredictionCubeCoefficient s f (fun w u => row w ((Fintype.equivFin S).symm u).val) w)
      (E w) := by
  unfold conditionalFiniteAverage masterChainWeightedMean
  congr 1
  funext x
  split_ifs
  · congr 1
    funext y
    exact (finset_product_fin_equiv S
      (fun u => masterPredictionCubeWeight F C label s f row w u x y)).symm
  · rfl

theorem MasterParameterConditions.replica_cube_root_majorant_tendsto
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
    (root : Fin q) (U : Finset (Fin q)) (hroot : root ∉ U) :
    Tendsto (fun w => conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => (masterPredictionCubeWeight F C label s f row w root x y - 1) *
        ∏ u ∈ U, (1 + masterPredictionCubeWeight F C label s f row w u x y)))
      atTop (𝓝 0) := by
  apply root_majorant_average_tendsto_zero
    (fun w => masterPrimeSlotsMass F w (fun j => gap w j))
    (masterMixedBaseMass H F index loc len) E
    (masterPredictionCubeWeight F C label s f row) root U hroot
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

end Hindman168
