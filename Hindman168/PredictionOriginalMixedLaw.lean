import Hindman168.MasterReplicaCubePositiveMean
import Hindman168.PredictionTranslationLaw
import Hindman168.ReplicaCubeEvaluations

/-!
# Exact enumeration of the original root and shift coordinate law

The master mixed-base representation has precisely one harmonic root.
The remaining coordinates retain their original locations and lengths.
Reindexing is an exact identity even for zero-length intervals.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionOriginalRootColumns (b d : ℕ) :
    Finset (Fin (Fintype.card (ReplicaCubeColumn b d))) :=
  {(Fintype.equivFin (ReplicaCubeColumn b d)) none}

noncomputable def predictionOriginalLocationFin {b d : ℕ}
    (A : Fin b × Fin d × Bool → ℤ)
    (j : Fin (Fintype.card (ReplicaCubeColumn b d))) : ℤ :=
  match (Fintype.equivFin (ReplicaCubeColumn b d)).symm j with
  | none => 0
  | some c => A c

noncomputable def predictionOriginalLengthFin {b d : ℕ} (T : Fin b → ℕ)
    (j : Fin (Fintype.card (ReplicaCubeColumn b d))) : ℕ :=
  match (Fintype.equivFin (ReplicaCubeColumn b d)).symm j with
  | none => 0
  | some c => T c.1

theorem predictionOriginalRootColumns_mem {b d : ℕ}
    (j : Fin (Fintype.card (ReplicaCubeColumn b d))) :
    j ∈ predictionOriginalRootColumns b d ↔
      (Fintype.equivFin (ReplicaCubeColumn b d)).symm j = none := by
  simp only [predictionOriginalRootColumns, Finset.mem_singleton]
  exact ⟨fun h => by rw [h]; exact Equiv.symm_apply_apply _ _,
    fun h => ((Equiv.apply_eq_iff_eq_symm_apply _).mpr h.symm).symm⟩

theorem prediction_original_mixed_base_eq {b d : ℕ} (X W : ℕ)
    (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ) :
    mixedIntegerBaseMass (predictionOriginalRootColumns b d) (fun _ => X) W
      (predictionOriginalLocationFin A) (predictionOriginalLengthFin T) =
    piMass (fun j => predictionOriginalColumnMass X W A T
      ((Fintype.equivFin (ReplicaCubeColumn b d)).symm j)) := by
  unfold mixedIntegerBaseMass
  congr 1
  funext j
  simp only [predictionOriginalRootColumns_mem]
  unfold predictionOriginalLocationFin predictionOriginalLengthFin
  cases h : (Fintype.equivFin (ReplicaCubeColumn b d)).symm j <;>
    simp [predictionOriginalColumnMass]

theorem prediction_original_mixed_expectation {b d : ℕ} (X W : ℕ)
    (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (f : (Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ) → ℝ) :
    expectation (mixedIntegerBaseMass (predictionOriginalRootColumns b d) (fun _ => X) W
      (predictionOriginalLocationFin A) (predictionOriginalLengthFin T)) f =
    expectation (piMass (predictionOriginalColumnMass X W A T))
      (fun z => f (fun j => z ((Fintype.equivFin (ReplicaCubeColumn b d)).symm j))) := by
  rw [prediction_original_mixed_base_eq, ← piMass_reindex, expectation_push]

end Hindman168
