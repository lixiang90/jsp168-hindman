import Hindman168.MaskUpdatedRowFunctions
import Hindman168.HarmonicSupportedCoordinates

/-! Exact original prime law for the new flattened tuple. The two fresh
primes are independent, while both branches retain the same old tuple.
The updated functions have their original majorant bound on the whole
new prime support, not just on a supplied joined tuple. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

namespace MaskColumnPlan

variable {m : ℕ} {S U : Finset (Fin (m + 1))}

noncomputable def freshTupleEquiv (P : MaskColumnPlan S U) (n : ℕ) :
    (Fin (2 + n) → ℕ) ≃ ((ℕ × ℕ) × (Fin n → ℕ)) where
  toFun ξ := (P.freshPair (maskFreshNewTuple ξ), maskFreshOldTuple ξ)
  invFun a := maskFreshTuple a.2 (P.freshValues a.1.1 a.1.2)
  left_inv ξ := by
    dsimp only
    rw [P.freshValues_pair, maskFreshTuple_projections]
  right_inv a := by
    rcases a with ⟨⟨p, q⟩, x⟩
    simp only [maskFreshNewTuple_join, maskFreshOldTuple_join, freshPair_values]

theorem freshTupleEquiv_symm_apply (P : MaskColumnPlan S U) (n : ℕ)
    (pq : ℕ × ℕ) (x : Fin n → ℕ) :
    (P.freshTupleEquiv n).symm (pq, x) = maskFreshTuple x (P.freshValues pq.1 pq.2) := rfl

end MaskColumnPlan

theorem maskFreshTuple_piMass {n : ℕ} (μ : Mass ℕ) (x : Fin n → ℕ) (y : Bool → ℕ) :
    piMass (fun _ : Fin (2 + n) => μ) (maskFreshTuple x y) =
      piMass (fun _ : Bool => μ) y * piMass (fun _ : Fin n => μ) x := by
  simp only [piMass_apply]
  have he := Fintype.prod_equiv (freshMaskSlotEquiv n)
    (fun s : Bool ⊕ Fin n => μ (Sum.elim y x s))
    (fun j : Fin (2 + n) => μ (maskFreshTuple x y j))
    (by intro s; simp [maskFreshTuple])
  rw [Fintype.prod_sum_type] at he
  exact he.symm

theorem maskFreshPrimeTupleLaw_split {m N n : ℕ} (gap : ℕ → Fin N)
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) (w : ℕ) :
    (monomialRowPrimeMass m gap (2 + n) w).mapDomain (P.freshTupleEquiv n) =
      tensor (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (monomialRowPrimeMass m gap n w) := by
  ext a
  rcases a with ⟨⟨p, q⟩, x⟩
  rw [Finsupp.mapDomain_equiv_apply]
  change piMass (fun _ : Fin (2 + n) => maskFreshPrimeMass (m := m) gap w)
      (maskFreshTuple x (P.freshValues p q)) =
    tensor (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
      (piMass (fun _ : Fin n => maskFreshPrimeMass (m := m) gap w)) ((p,q),x)
  rw [maskFreshTuple_piMass, tensor_apply, tensor_apply, piMass_apply, Fintype.prod_bool]
  cases P <;> simp only [MaskColumnPlan.freshValues, Bool.false_eq_true, if_false, if_true]
  all_goals ring

theorem maskFreshPrimeTupleLaw_expectation {m N n : ℕ} (gap : ℕ → Fin N)
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) (w : ℕ)
    (H : (Fin (2 + n) → ℕ) → ℝ) :
    expectation (monomialRowPrimeMass m gap (2 + n) w) H =
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => expectation (monomialRowPrimeMass m gap n w)
          (fun x => H (maskFreshTuple x (P.freshValues pq.1 pq.2)))) := by
  have he := congrArg (fun μ => expectation μ (fun a => H ((P.freshTupleEquiv n).symm a)))
    (maskFreshPrimeTupleLaw_split gap P w)
  rw [expectation_push, expectation_tensor] at he
  simpa only [Equiv.symm_apply_apply, MaskColumnPlan.freshTupleEquiv_symm_apply] using he

theorem maskFreshPrimeTuple_support_projections {m N n : ℕ} (gap : ℕ → Fin N)
    (w : ℕ) (ξ : Fin (2 + n) → ℕ) (hξ : ξ ∈ (monomialRowPrimeMass m gap (2 + n) w).support) :
    maskFreshOldTuple ξ ∈ (monomialRowPrimeMass m gap n w).support ∧
    ∀ b, maskFreshNewTuple ξ b ∈ primePool
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper := by
  have hcoord : ∀ j, ξ j ∈ (maskFreshPrimeMass (m := m) gap w).support :=
    fun j => piMass_mem_support_coordinate _ ξ hξ j
  constructor
  · apply Finsupp.mem_support_iff.mpr
    change (∏ j : Fin n, maskFreshPrimeMass (m := m) gap w (maskFreshOldTuple ξ j)) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Finsupp.mem_support_iff.mp (hcoord (freshMaskOldSlot n j))
  · intro b
    exact primePoolMass_support _ _ (hcoord (freshMaskNewSlot n b))

theorem maskFreshPrimeTuple_support_pair {m N n : ℕ} (gap : ℕ → Fin N)
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) (w : ℕ)
    (ξ : Fin (2 + n) → ℕ) (hξ : ξ ∈ (monomialRowPrimeMass m gap (2 + n) w).support) :
    (P.freshPair (maskFreshNewTuple ξ)).1 ∈ primePool
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper ∧
    (P.freshPair (maskFreshNewTuple ξ)).2 ∈ primePool
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper := by
  have hs := (maskFreshPrimeTuple_support_projections gap w ξ hξ).2
  cases P with
  | outside u hu hU => exact ⟨hs false, hs true⟩
  | balanced u v hu hv huU hvU hne => exact ⟨hs true, hs false⟩

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskUpdatedRowFunctions_eventually_support_bound :
    ∀ᶠ w in atTop, ∀ (n r : ℕ)
      (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
      (S U : Finset (Fin (m + 1))) (P : MaskColumnPlan S U),
      ∀ f : (Fin n → ℕ) → Fin r → ℤ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap n w).support, ∀ i t,
        |f x i t| ≤ maskFamilyRowMajorant gap C F w i t) →
      ∀ ξ ∈ (monomialRowPrimeMass m gap (2 + n) w).support, ∀ i t,
      |maskUpdatedRowFunctions gap C P F w f ξ i t| ≤
        maskFamilyRowMajorant gap C (F.flattenedMaskStep P.tag) w i t := by
  filter_upwards [maskUpdatedRowFunctions_eventually_join_bound gap C hC htail] with w hw
  intro n r F S U P f hf ξ hξ i t
  have hx := (maskFreshPrimeTuple_support_projections gap w ξ hξ).1
  have hpq := maskFreshPrimeTuple_support_pair gap P w ξ hξ
  have he : maskFreshTuple (maskFreshOldTuple ξ)
      (P.freshValues (P.freshPair (maskFreshNewTuple ξ)).1 (P.freshPair (maskFreshNewTuple ξ)).2) = ξ := by
    rw [P.freshValues_pair, maskFreshTuple_projections]
  have hb := hw n r F S U P _ hpq.1 _ hpq.2 f (maskFreshOldTuple ξ) (hf _ hx) i t
  simpa only [he] using hb

include hC htail in
theorem maskStageUpdatedRowFunctions_eventually_support_bound
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ i t, |f x i t| ≤ maskStageRowMajorant S hS gap C k w i t) →
      ∀ ξ ∈ (monomialRowPrimeMass m gap ((maskPrefixRowStage S hS k).step hS U).primeArity w).support,
      ∀ i : Fin ((maskPrefixRowStage S hS k).step hS U).rowCount, ∀ t,
      |maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS)
        (maskPrefixRowStage S hS k).rows w f ξ i t| ≤
      maskFamilyRowMajorant gap C ((maskPrefixRowStage S hS k).step hS U).rows w i t := by
  filter_upwards [maskUpdatedRowFunctions_eventually_support_bound gap C hC htail] with w hw
  intro k U f hf ξ hξ i t
  exact hw _ _ (maskPrefixRowStage S hS k).rows S U (chosenMaskColumnPlan S U hS) f hf ξ hξ i t

end Hindman168
