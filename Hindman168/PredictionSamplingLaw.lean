import Hindman168.PredictionStagePairValues

/-!
# The full copied coordinate law equals the conditional pair law

Original columns and direction pairs are recovered by an explicit
bijection. Product coefficients agree exactly; no normalized marginals
or independence conclusions are supplied as additional hypotheses.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionSampleColumns {b d h : ℕ}
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) : CopiedReplicaCubeColumn b d h → ℤ :=
  Sum.elim z (fun ib => predictionPairValues v ib.1 ib.2)

noncomputable def predictionSampleCoordinates {b d h : ℕ}
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) :
    Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ :=
  fun j => predictionSampleColumns z v ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)

noncomputable def predictionSamplingEquiv (b d h : ℕ) :
    (CopiedReplicaCubeColumn b d h → ℤ) ≃ ((ReplicaCubeColumn b d → ℤ) × (Fin h → ℤ × ℤ)) where
  toFun a := (fun col => a (.inl col), fun i => (a (.inr (i, false)), a (.inr (i, true))))
  invFun zv := predictionSampleColumns zv.1 zv.2
  left_inv a := by
    funext col
    cases col with
    | inl c => rfl
    | inr ib => rcases ib with ⟨i, bit⟩; cases bit <;> rfl
  right_inv zv := by
    apply Prod.ext
    · rfl
    · funext i; rfl

noncomputable def predictionComponentMass {b d h : ℕ}
    (μ : ReplicaCubeColumn b d → Mass ℤ) (τ : Fin h → Mass ℤ) :
    CopiedReplicaCubeColumn b d h → Mass ℤ :=
  Sum.elim μ (fun ib => τ ib.1)

theorem predictionSamplingEquiv_law {b d h : ℕ}
    (μ : ReplicaCubeColumn b d → Mass ℤ) (τ : Fin h → Mass ℤ) :
    (piMass (predictionComponentMass μ τ)).mapDomain (predictionSamplingEquiv b d h) =
      tensor (piMass μ) (piMass (fun i => tensor (τ i) (τ i))) := by
  ext zv
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply, piMass_apply]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type,
    predictionComponentMass, predictionSamplingEquiv, predictionSampleColumns,
    Sum.elim_inl, Sum.elim_inr]
  congr 1
  apply Fintype.prod_congr
  intro i
  simp only [Fintype.prod_bool, predictionPairValues, tensor_apply]
  exact mul_comm _ _

theorem predictionSampleCoordinates_eval {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) :
    (∑ j, copiedReplicaCubeFinCoefficient M dir r j * predictionSampleCoordinates z v j) =
      copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v) := by
  unfold predictionSampleCoordinates
  rw [copiedReplicaCubeFinCoefficient_eval]
  exact copiedReplicaCubeCoefficient_eval M dir r z (predictionPairValues v)

theorem predictionSampleCoordinates_law {b d h : ℕ}
    (μ : ReplicaCubeColumn b d → Mass ℤ) (τ : Fin h → Mass ℤ) (f : (Fin (Fintype.card
      (CopiedReplicaCubeColumn b d h)) → ℤ) → ℝ) :
    expectation (piMass (fun j => predictionComponentMass μ τ
      ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j))) f =
      expectation (piMass μ) (fun z => expectation (piMass (fun i => tensor (τ i) (τ i)))
        (fun v => f (predictionSampleCoordinates z v))) := by
  let e := Fintype.equivFin (CopiedReplicaCubeColumn b d h)
  have hfin := piMass_reindex (predictionComponentMass μ τ) e.symm
  have hc := congrArg (fun ρ => expectation ρ f) hfin
  rw [expectation_push] at hc
  rw [← hc]
  have hs := congrArg (fun ρ => expectation ρ
    (fun zv => f (predictionSampleCoordinates zv.1 zv.2))) (predictionSamplingEquiv_law μ τ)
  rw [expectation_push, expectation_tensor] at hs
  have hrec (a : CopiedReplicaCubeColumn b d h → ℤ) :
      predictionSampleCoordinates ((predictionSamplingEquiv b d h) a).1
        ((predictionSamplingEquiv b d h) a).2 = fun j => a (e.symm j) := by
    funext j
    exact congrFun ((predictionSamplingEquiv b d h).symm_apply_apply a) (e.symm j)
  simp_rw [hrec] at hs
  exact hs

end Hindman168
