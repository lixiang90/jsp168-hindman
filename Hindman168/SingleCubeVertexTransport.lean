import Hindman168.SingleCubeSamplingLaw

/-! Reindex a one-replica cube by all Boolean vertices, including its root.
The exact product and original harmonic/pair expectation are preserved. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def cubeSubsetBoolEquiv (d : ℕ) : Finset (Fin d) ≃ (Fin d → Bool) where
  toFun S := fun j => decide (j ∈ S)
  invFun η := Finset.univ.filter (fun j => η j = true)
  left_inv S := by ext j; simp
  right_inv η := by
    funext j
    cases hj : η j <;> simp [hj]

noncomputable def singleCubeRowFinsetEquiv (d : ℕ) : ReplicaCubeRow 1 d ≃ Finset (Fin d) where
  toFun r := match r with | none => ∅ | some (_, S) => S.val
  invFun S := if h : S.Nonempty then some (0, ⟨S, h⟩) else none
  left_inv r := by
    cases r with
    | none => simp
    | some r =>
      rcases r with ⟨q, S⟩
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      dsimp
      rw [dif_pos S.property]
  right_inv S := by
    by_cases h : S.Nonempty
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      exact (Finset.not_nonempty_iff_eq_empty.mp h).symm

noncomputable def singleCubeRowBoolEquiv (d : ℕ) : ReplicaCubeRow 1 d ≃ (Fin d → Bool) :=
  (singleCubeRowFinsetEquiv d).trans (cubeSubsetBoolEquiv d)

theorem singleCube_evaluation {d : ℕ} (M : ℤ) (r : ReplicaCubeRow 1 d)
    (y : ℤ) (v : Fin d → ℤ × ℤ) :
    replicaCubeEval (fun _ : Fin 1 => M) r (singleCubeSampleColumns y v) =
      y + M * ∑ j, if singleCubeRowBoolEquiv d r j then (v j).2 - (v j).1 else 0 := by
  cases r with
  | none => simp [replicaCubeEval_root, singleCubeSampleColumns, singleCubeRowBoolEquiv,
      singleCubeRowFinsetEquiv, cubeSubsetBoolEquiv]
  | some r =>
    rcases r with ⟨q, S⟩
    rw [replicaCubeEval_vertex]
    have hb (j : Fin d) : singleCubeRowBoolEquiv d (some (q, S)) j = decide (j ∈ S.val) := rfl
    simp_rw [hb]
    change y + M * (∑ j ∈ S.val, ((v j).2 - (v j).1)) =
      y + M * ∑ j, if decide (j ∈ S.val) then (v j).2 - (v j).1 else 0
    simp only [decide_eq_true_eq]
    rw [← Finset.sum_filter]
    simp

theorem singleCube_bool_product {d : ℕ} (M : ℤ) (f : ℤ → ℝ) (y : ℤ) (v : Fin d → ℤ × ℤ) :
    (∏ r : ReplicaCubeRow 1 d, f (replicaCubeEval (fun _ : Fin 1 => M) r (singleCubeSampleColumns y v))) =
      ∏ η : Fin d → Bool, f (y + M * ∑ j, if η j then (v j).2 - (v j).1 else 0) := by
  exact Fintype.prod_equiv (singleCubeRowBoolEquiv d) _ _ (fun r => by rw [singleCube_evaluation])

theorem singleCube_product_expectation (d X W T : ℕ) (M : ℤ) (f : ℤ → ℝ) :
    expectation (piMass (predictionOriginalColumnMass X W (fun _ : Fin 1 × Fin d × Bool => 0) (fun _ => T)))
      (fun z => ∏ r : ReplicaCubeRow 1 d, f (replicaCubeEval (fun _ : Fin 1 => M) r z)) =
    expectation (piMass (fun _ : Fin d => tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T)))
      (fun v => expectation (integerMass X W) (fun y =>
        ∏ η : Fin d → Bool, f (y + M * ∑ j, if η j then (v j).2 - (v j).1 else 0))) := by
  rw [singleCube_original_expectation, expectation_comm]
  apply congrArg (expectation (piMass (fun _ : Fin d => tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T))))
  funext v
  apply congrArg (expectation (integerMass X W))
  funext y
  exact singleCube_bool_product M f y v

end Hindman168
