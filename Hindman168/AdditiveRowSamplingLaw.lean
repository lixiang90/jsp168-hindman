import Hindman168.AdditiveRowCopiedCoefficients
import Hindman168.PredictionSamplingLaw

/-!
# General original integer coordinates and independent direction pairs

Original columns and direction pairs are recovered by an explicit
bijection. Product coefficients agree exactly; no normalized marginals
or independence conclusions are supplied as additional hypotheses.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def additiveSampleColumns {b c : ℕ}
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) : AdditiveCopiedColumn b c → ℤ :=
  Sum.elim z (fun ib => predictionPairValues v ib.1 ib.2)

noncomputable def additiveSampleCoordinates {b c : ℕ}
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) :
    Fin (Fintype.card (AdditiveCopiedColumn b c)) → ℤ :=
  fun j => additiveSampleColumns z v ((Fintype.equivFin (AdditiveCopiedColumn b c)).symm j)

noncomputable def additiveSamplingEquiv (b c : ℕ) :
    (AdditiveCopiedColumn b c → ℤ) ≃ ((Fin c → ℤ) × (Fin b → ℤ × ℤ)) where
  toFun a := (fun col => a (.inl col), fun i => (a (.inr (i, false)), a (.inr (i, true))))
  invFun zv := additiveSampleColumns zv.1 zv.2
  left_inv a := by
    funext col
    cases col with
    | inl c => rfl
    | inr ib => rcases ib with ⟨i, bit⟩; cases bit <;> rfl
  right_inv zv := by
    apply Prod.ext
    · rfl
    · funext i; rfl

noncomputable def additiveComponentMass {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) :
    AdditiveCopiedColumn b c → Mass ℤ :=
  Sum.elim μ (fun ib => τ ib.1)

theorem additiveSamplingEquiv_law {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) :
    (piMass (additiveComponentMass μ τ)).mapDomain (additiveSamplingEquiv b c) =
      tensor (piMass μ) (piMass (fun i => tensor (τ i) (τ i))) := by
  ext zv
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply, piMass_apply]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type,
    additiveComponentMass, additiveSamplingEquiv, additiveSampleColumns,
    Sum.elim_inl, Sum.elim_inr]
  congr 1
  apply Fintype.prod_congr
  intro i
  simp only [Fintype.prod_bool, predictionPairValues, tensor_apply]
  exact mul_comm _ _

theorem additiveSampleCoordinates_eval {b c : ℕ} (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b))
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) :
    (∑ j, D.copiedFinCoefficient r j * additiveSampleCoordinates z v j) =
      D.translatedForm r.val.1 r.val.2 z (predictionPairValues v) := by
  unfold additiveSampleCoordinates
  rw [D.copiedFinCoefficient_eval]
  exact D.copiedCoefficient_eval r z (predictionPairValues v)

theorem additiveSampleCoordinates_law {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) (f : (Fin (Fintype.card
      (AdditiveCopiedColumn b c)) → ℤ) → ℝ) :
    expectation (piMass (fun j => additiveComponentMass μ τ
      ((Fintype.equivFin (AdditiveCopiedColumn b c)).symm j))) f =
      expectation (piMass μ) (fun z => expectation (piMass (fun i => tensor (τ i) (τ i)))
        (fun v => f (additiveSampleCoordinates z v))) := by
  let e := Fintype.equivFin (AdditiveCopiedColumn b c)
  have hfin := piMass_reindex (additiveComponentMass μ τ) e.symm
  have hc := congrArg (fun ρ => expectation ρ f) hfin
  rw [expectation_push] at hc
  rw [← hc]
  have hs := congrArg (fun ρ => expectation ρ
    (fun zv => f (additiveSampleCoordinates zv.1 zv.2))) (additiveSamplingEquiv_law μ τ)
  rw [expectation_push, expectation_tensor] at hs
  have hrec (a : AdditiveCopiedColumn b c → ℤ) :
      additiveSampleCoordinates ((additiveSamplingEquiv b c) a).1
        ((additiveSamplingEquiv b c) a).2 = fun j => a (e.symm j) := by
    funext j
    exact congrFun ((additiveSamplingEquiv b c).symm_apply_apply a) (e.symm j)
  simp_rw [hrec] at hs
  exact hs

end Hindman168
