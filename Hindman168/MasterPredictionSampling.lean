import Hindman168.PredictionSamplingLaw

/-!
# The actual mixed master law in original columns and direction pairs

All harmonic and interval coordinates keep their original master labels,
locations and lengths. Direction branches are auxiliary interval columns
with the same location and length. Their factorization into independent
pairs is derived from the exact coefficient law.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionColumnIndex {b d h : ℕ} (col : CopiedReplicaCubeColumn b d h) :
    Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) := Fintype.equivFin _ col

noncomputable def masterPredictionOriginalCoordinateMass {N r b d h : ℕ}
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (F : MasterParameterFamily)
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ) (col : ReplicaCubeColumn b d) : Mass ℤ :=
  let j := predictionColumnIndex (Sum.inl col : CopiedReplicaCubeColumn b d h)
  if j ∈ H then integerMass (F.cutoff w (index w j).val) (primorial w)
  else uniformIntervalMass (loc w x j) (len w x j)

noncomputable def masterPredictionDirectionMass {r b d h : ℕ}
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ) (i : Fin h) : Mass ℤ :=
  uniformIntervalMass (loc w x (predictionColumnIndex (.inr (i, false))))
    (len w x (predictionColumnIndex (.inr (i, false))))

theorem masterPredictionDirectionMass_nonneg {r b d h : ℕ}
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ) (i : Fin h) (t : ℤ) :
    0 ≤ masterPredictionDirectionMass loc len w x i t := uniformIntervalMass_nonneg _ _ _

theorem masterPredictionDirectionMass_total {r b d h : ℕ}
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ) (i : Fin h)
    (hpos : 0 < len w x (predictionColumnIndex (.inr (i, false)))) :
    total (masterPredictionDirectionMass loc len w x i) = 1 := uniformIntervalMass_total _ hpos

theorem master_prediction_component_mass_eq {N r b d h : ℕ}
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (F : MasterParameterFamily)
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hlen : ∀ i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false)))) :
    masterMixedBaseMass H F index loc len w x = piMass (fun j =>
      predictionComponentMass (masterPredictionOriginalCoordinateMass H F index loc len w x)
        (masterPredictionDirectionMass loc len w x)
        ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)) := by
  have hp (col : CopiedReplicaCubeColumn b d h) :
      predictionComponentMass (masterPredictionOriginalCoordinateMass H F index loc len w x)
        (masterPredictionDirectionMass loc len w x) col =
      if predictionColumnIndex col ∈ H then
        integerMass (F.cutoff w (index w (predictionColumnIndex col)).val) (primorial w)
      else uniformIntervalMass (loc w x (predictionColumnIndex col))
        (len w x (predictionColumnIndex col)) := by
    cases col with
    | inl c => rfl
    | inr ib =>
      rcases ib with ⟨i, bit⟩
      simp only [predictionComponentMass, Sum.elim_inr, masterPredictionDirectionMass,
        if_neg (haux i bit), hloc i bit, hlen i bit]
  unfold masterMixedBaseMass mixedIntegerBaseMass
  congr 1
  funext j
  rw [hp]
  simp only [predictionColumnIndex, Equiv.apply_symm_apply]

theorem master_prediction_sampling_law {N r b d h : ℕ}
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (F : MasterParameterFamily)
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (w : ℕ) (x : Fin r → ℕ)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hlen : ∀ i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (g : (Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ) → ℝ) :
    expectation (masterMixedBaseMass H F index loc len w x) g =
      expectation (piMass (masterPredictionOriginalCoordinateMass H F index loc len w x))
        (fun z => expectation (piMass (fun i => tensor (masterPredictionDirectionMass loc len w x i)
          (masterPredictionDirectionMass loc len w x i))) (fun v => g (predictionSampleCoordinates z v))) := by
  rw [master_prediction_component_mass_eq H F index loc len w x haux hloc hlen]
  exact predictionSampleCoordinates_law _ _ g

end Hindman168
