import Hindman168.RootSmoothedAdditiveRows
import Hindman168.AdditiveRowSamplingLaw

/-! Exact independent original coordinates, paired old directions and
paired root translations, recovered by a bijection. No probability or
asymptotic claim is assumed for this finite law identity. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def rootPairValues (u : ℤ × ℤ) (bit : Bool) : ℤ := if bit then u.2 else u.1

noncomputable def rootSmoothedSampleColumns {b c : ℕ}
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (u : ℤ × ℤ) :
    RootSmoothedAdditiveColumn b c → ℤ := Sum.elim (additiveSampleColumns z v) (rootPairValues u)

noncomputable def rootSmoothedSampleCoordinates {b c : ℕ}
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (u : ℤ × ℤ) :
    Fin (Fintype.card (RootSmoothedAdditiveColumn b c)) → ℤ :=
  fun j => rootSmoothedSampleColumns z v u
    ((Fintype.equivFin (RootSmoothedAdditiveColumn b c)).symm j)

noncomputable def rootSmoothedSamplingEquiv (b c : ℕ) :
    (RootSmoothedAdditiveColumn b c → ℤ) ≃
      (((Fin c → ℤ) × (Fin b → ℤ × ℤ)) × (ℤ × ℤ)) where
  toFun a := (additiveSamplingEquiv b c (fun j => a (.inl j)), (a (.inr false), a (.inr true)))
  invFun zvu := rootSmoothedSampleColumns zvu.1.1 zvu.1.2 zvu.2
  left_inv a := by
    funext col
    cases col with
    | inl col =>
      cases col with
      | inl j => rfl
      | inr kb => rcases kb with ⟨k, bit⟩; cases bit <;> rfl
    | inr bit => cases bit <;> rfl
  right_inv zvu := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext k; rfl
    · rfl

noncomputable def rootSmoothedComponentMass {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) (ρ : Mass ℤ) :
    RootSmoothedAdditiveColumn b c → Mass ℤ :=
  Sum.elim (additiveComponentMass μ τ) (fun _ => ρ)

theorem rootSmoothedSamplingEquiv_law {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) (ρ : Mass ℤ) :
    (piMass (rootSmoothedComponentMass μ τ ρ)).mapDomain (rootSmoothedSamplingEquiv b c) =
      tensor (tensor (piMass μ) (piMass (fun k => tensor (τ k) (τ k)))) (tensor ρ ρ) := by
  ext zvu
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [piMass_apply, tensor_apply, rootSmoothedSamplingEquiv,
    rootSmoothedSampleColumns, rootSmoothedComponentMass, Fintype.prod_sum_type,
    Fintype.prod_prod_type, additiveComponentMass, additiveSampleColumns,
    Sum.elim_inl, Sum.elim_inr]
  congr 1
  · congr 1
    apply Fintype.prod_congr
    intro k
    simp only [Fintype.prod_bool, predictionPairValues]
    exact mul_comm _ _
  · simp only [Fintype.prod_bool]
    exact mul_comm _ _

theorem rootSmoothedSampleCoordinates_eval {b c : ℕ} (D : AdditiveRowData b c)
    (v₀ : Fin c → ℤ) (r : RootSmoothedAdditiveCopy b)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (u : ℤ × ℤ) :
    (∑ j, D.rootSmoothedFinCoefficient v₀ r j * rootSmoothedSampleCoordinates z v u j) =
      D.translatedForm r.val.1.val.1 r.val.1.val.2
        (fun j => z j + rootPairValues u r.val.2 * v₀ j) (predictionPairValues v) := by
  unfold rootSmoothedSampleCoordinates
  rw [D.rootSmoothedFinCoefficient_eval]
  exact D.rootSmoothedCoefficient_eval_translate v₀ r z (predictionPairValues v) (rootPairValues u)

theorem rootSmoothedSampleCoordinates_law {b c : ℕ}
    (μ : Fin c → Mass ℤ) (τ : Fin b → Mass ℤ) (ρ : Mass ℤ)
    (f : (Fin (Fintype.card (RootSmoothedAdditiveColumn b c)) → ℤ) → ℝ) :
    expectation (piMass (fun j => rootSmoothedComponentMass μ τ ρ
      ((Fintype.equivFin (RootSmoothedAdditiveColumn b c)).symm j))) f =
      expectation (piMass μ) (fun z => expectation (piMass (fun k => tensor (τ k) (τ k)))
        (fun v => expectation ρ (fun u₀ => expectation ρ
          (fun u₁ => f (rootSmoothedSampleCoordinates z v (u₀, u₁)))))) := by
  let e := Fintype.equivFin (RootSmoothedAdditiveColumn b c)
  have hr := congrArg (fun θ => expectation θ f)
    (piMass_reindex (rootSmoothedComponentMass μ τ ρ) e.symm)
  rw [expectation_push] at hr
  rw [← hr]
  have hs := congrArg (fun θ => expectation θ
    (fun zvu => f (rootSmoothedSampleCoordinates zvu.1.1 zvu.1.2 zvu.2)))
      (rootSmoothedSamplingEquiv_law μ τ ρ)
  simp only [expectation_push, expectation_tensor] at hs
  have hrec (a : RootSmoothedAdditiveColumn b c → ℤ) :
      rootSmoothedSampleCoordinates ((rootSmoothedSamplingEquiv b c) a).1.1
        ((rootSmoothedSamplingEquiv b c) a).1.2 ((rootSmoothedSamplingEquiv b c) a).2 =
          fun j => a (e.symm j) := by
    funext j
    exact congrFun ((rootSmoothedSamplingEquiv b c).symm_apply_apply a) (e.symm j)
  simp_rw [hrec] at hs
  exact hs

end Hindman168
