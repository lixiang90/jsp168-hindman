import Hindman168.MasterCommonTailPrediction

/-!
# Concrete copied boxes for original shifts and square-root directions

The only harmonic column is the root y. Original shifts retain their own
replica length. Every inserted direction uses two independent intervals
[0,Nat.sqrt(T_q)) of identical length. The structural hypotheses of the
master elimination interface follow from these explicit coordinates.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionBoxRootColumns (b d h : ℕ) :
    Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) :=
  {predictionColumnIndex (.inl none : CopiedReplicaCubeColumn b d h)}

noncomputable def predictionBoxLocation {b d h : ℕ}
    (A : Fin b × Fin d × Bool → ℤ) : CopiedReplicaCubeColumn b d h → ℤ
  | .inl none => 0
  | .inl (some c) => A c
  | .inr _ => 0

noncomputable def predictionBoxLength {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ) : CopiedReplicaCubeColumn b d h → ℕ
  | .inl none => 1
  | .inl (some (q, _, _)) => T q
  | .inr (i, _) => Nat.sqrt (T (dir i).1)

noncomputable def predictionBoxLocationFin {b d h : ℕ}
    (A : Fin b × Fin d × Bool → ℤ) (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) : ℤ :=
  predictionBoxLocation A ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)

noncomputable def predictionBoxLengthFin {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ)
    (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) : ℕ :=
  predictionBoxLength dir T ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)

theorem predictionBoxRootColumns_mem_iff {b d h : ℕ} (col : CopiedReplicaCubeColumn b d h) :
    predictionColumnIndex col ∈ predictionBoxRootColumns b d h ↔ col = .inl none := by
  simp only [predictionBoxRootColumns, Finset.mem_singleton]
  exact (Fintype.equivFin (CopiedReplicaCubeColumn b d h)).injective.eq_iff

theorem prediction_box_auxiliary_columns {b d h : ℕ} (i : Fin h) (bit : Bool) :
    predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉
      predictionBoxRootColumns b d h := by
  rw [predictionBoxRootColumns_mem_iff]
  simp

theorem prediction_box_locations_pair {b d h : ℕ}
    (A : Fin b × Fin d × Bool → ℤ) (i : Fin h) (bit : Bool) :
    predictionBoxLocationFin A (predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h)) =
      predictionBoxLocationFin A (predictionColumnIndex (.inr (i, false) : CopiedReplicaCubeColumn b d h)) := by
  simp [predictionBoxLocationFin, predictionColumnIndex, predictionBoxLocation]

theorem prediction_box_lengths_pair {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ) (i : Fin h) (bit : Bool) :
    predictionBoxLengthFin dir T (predictionColumnIndex (.inr (i, bit))) =
      predictionBoxLengthFin dir T (predictionColumnIndex (.inr (i, false))) := by
  simp [predictionBoxLengthFin, predictionColumnIndex, predictionBoxLength]

theorem prediction_box_lengths_mono {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (Tmin T : Fin b → ℕ) (hT : ∀ q, Tmin q ≤ T q)
    (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) :
    predictionBoxLengthFin dir Tmin j ≤ predictionBoxLengthFin dir T j := by
  obtain ⟨col, rfl⟩ := (Fintype.equivFin (CopiedReplicaCubeColumn b d h)).surjective j
  simp only [predictionBoxLengthFin, Equiv.symm_apply_apply]
  cases col with
  | inl c => cases c with
    | none => exact le_rfl
    | some c => exact hT c.1
  | inr ib => exact Nat.sqrt_le_sqrt (hT (dir ib.1).1)

theorem prediction_box_lower_growth {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (Tmin : ℕ → Fin b → ℕ) (V : ℕ → ℕ)
    (hg : ∀ q, PowerDominates atTop (fun w => (Tmin w q : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h)))
    (hj : j ∉ predictionBoxRootColumns b d h) :
    PowerDominates atTop (fun w => (predictionBoxLengthFin dir (Tmin w) j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) := by
  obtain ⟨col, rfl⟩ := (Fintype.equivFin (CopiedReplicaCubeColumn b d h)).surjective j
  simp only [predictionBoxLengthFin, Equiv.symm_apply_apply]
  cases col with
  | inl c => cases c with
    | none => exact False.elim (hj (by simp [predictionBoxRootColumns, predictionColumnIndex]))
    | some c => exact hg c.1
  | inr ib => exact (hg (dir ib.1).1).nat_sqrt (Eventually.of_forall (fun _ => Nat.cast_nonneg _))

theorem prediction_box_original_mass {N r b d h : ℕ}
    (F : MasterParameterFamily) (root : ℕ → Fin N)
    (dir : Fin h → Fin b × CubeVertex d)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (w : ℕ) (x : Fin r → ℕ)
    (col : ReplicaCubeColumn b d) :
    masterPredictionOriginalCoordinateMass (predictionBoxRootColumns b d h) F
      (fun w _ => root w) (fun w x => predictionBoxLocationFin (A w x))
      (fun w x => predictionBoxLengthFin dir (T w x)) w x col =
      predictionOriginalColumnMass (F.cutoff w (root w).val) (primorial w) (A w x) (T w x) col := by
  cases col with
  | none => simp [masterPredictionOriginalCoordinateMass, predictionBoxRootColumns,
      predictionOriginalColumnMass]
  | some c =>
    have hc : predictionColumnIndex (.inl (some c) : CopiedReplicaCubeColumn b d h) ∉
        predictionBoxRootColumns b d h := by rw [predictionBoxRootColumns_mem_iff]; simp
    simp only [masterPredictionOriginalCoordinateMass, if_neg hc]
    simp [predictionBoxLocationFin,
      predictionBoxLengthFin, predictionColumnIndex, predictionBoxLocation,
      predictionBoxLength, predictionOriginalColumnMass]

theorem prediction_box_direction_mass {r b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (w : ℕ) (x : Fin r → ℕ) (i : Fin h) :
    masterPredictionDirectionMass (fun w x => predictionBoxLocationFin (A w x))
      (fun w x => predictionBoxLengthFin dir (T w x)) w x i =
      uniformIntervalMass 0 (Nat.sqrt (T w x (dir i).1)) := by
  simp [masterPredictionDirectionMass, predictionBoxLocationFin, predictionBoxLengthFin,
    predictionColumnIndex, predictionBoxLocation, predictionBoxLength]

theorem prediction_box_stage_average {N m r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (primeGap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (root : ℕ → Fin N) (dir : Fin h → Fin b × CubeVertex d)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (w : ℕ) (K : Finset (Fin h)) :
    masterPredictionStageAverage F C label primeGap s f dir (predictionBoxRootColumns b d h)
      (fun w _ => root w) (fun w x => predictionBoxLocationFin (A w x))
      (fun w x => predictionBoxLengthFin dir (T w x)) E G w K =
      expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
        expectation (piMass (predictionOriginalColumnMass (F.cutoff w (root w).val)
          (primorial w) (A w x) (T w x)))
          (fun z => expectation (predictionSquareRootPairMass dir (T w x))
            (fun v => predictionEliminationIntegrand
              (fun q => predictionCubeModulus w (s w q) (f q) x) dir K z v (G w x)
              (fun base t => 1 + integerDivisorMask
                (masterPredictionBaseDivisorMass F C label w base) t))) else 0) := by
  unfold masterPredictionStageAverage conditionalFiniteAverage
  congr 1
  funext x
  have hm : masterPredictionOriginalCoordinateMass (predictionBoxRootColumns b d h) F
      (fun w _ => root w) (fun w x => predictionBoxLocationFin (A w x))
      (fun w x => predictionBoxLengthFin dir (T w x)) w x =
      predictionOriginalColumnMass (F.cutoff w (root w).val) (primorial w) (A w x) (T w x) := by
    funext col
    exact prediction_box_original_mass F root dir A T w x col
  have hd : piMass (fun i => tensor
      (masterPredictionDirectionMass (fun w x => predictionBoxLocationFin (A w x))
        (fun w x => predictionBoxLengthFin dir (T w x)) w x i)
      (masterPredictionDirectionMass (fun w x => predictionBoxLocationFin (A w x))
        (fun w x => predictionBoxLengthFin dir (T w x)) w x i)) =
      predictionSquareRootPairMass dir (T w x) := by
    unfold predictionSquareRootPairMass
    congr 1
    funext i
    rw [prediction_box_direction_mass]
  simp only [hm, hd]

end Hindman168
