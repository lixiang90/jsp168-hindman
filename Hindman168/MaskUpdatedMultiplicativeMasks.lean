import Hindman168.MaskMonomialSubstitutions

/-! Surviving multiplicative masks are genuine functions of a support
monomial and the new prime tuple. Both copies use the same old tuple;
no change of monomial support or prime sampling law is made. -/

namespace Hindman168

open scoped BigOperators Classical

variable {m n : ℕ}

noncomputable def maskMultiplicativeProduct (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ V ∈ T, b x V (maskCoordinateMonomial V z)

noncomputable def maskUpdatedMultiplicativeMasks {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (ξ : Fin (2 + n) → ℕ) (V : Finset (Fin (m + 1))) (t : ℤ) : ℝ :=
  let x := maskFreshOldTuple ξ
  let pq := P.freshPair (maskFreshNewTuple ξ)
  b x V (P.monomialScalar pq.1 pq.2 V * t) *
    b x V (P.monomialScalar pq.2 pq.1 V * t)

theorem maskUpdatedMultiplicativeMasks_join {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (x : Fin n → ℕ) (p q : ℕ) (V : Finset (Fin (m + 1))) (t : ℤ) :
    maskUpdatedMultiplicativeMasks P b (maskFreshTuple x (P.freshValues p q)) V t =
      b x V (P.monomialScalar p q V * t) * b x V (P.monomialScalar q p V * t) := by
  simp only [maskUpdatedMultiplicativeMasks, maskFreshOldTuple_join, maskFreshNewTuple_join,
    MaskColumnPlan.freshPair_values]

theorem maskUpdatedMultiplicativeMasks_evaluated {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (x : Fin n → ℕ) (p q : ℕ) (V : Finset (Fin (m + 1))) (z : Fin (m + 1) → ℤ) :
    maskUpdatedMultiplicativeMasks P b (maskFreshTuple x (P.freshValues p q)) V
      (maskCoordinateMonomial V z) =
      b x V (maskCoordinateMonomial V (P.absorbedCoordinates p q z)) *
        b x V (maskCoordinateMonomial V (P.absorbedCoordinates q p z)) := by
  rw [maskUpdatedMultiplicativeMasks_join, P.monomial_absorbed, P.monomial_absorbed]

theorem maskMultiplicativeProduct_update {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (x : Fin n → ℕ) (p q : ℕ) (z : Fin (m + 1) → ℤ) :
    maskMultiplicativeProduct T (maskUpdatedMultiplicativeMasks P b)
      (maskFreshTuple x (P.freshValues p q)) z =
      maskMultiplicativeProduct T b x (P.absorbedCoordinates p q z) *
        maskMultiplicativeProduct T b x (P.absorbedCoordinates q p z) := by
  unfold maskMultiplicativeProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro V _
  exact maskUpdatedMultiplicativeMasks_evaluated P b x p q V z

theorem maskMultiplicativeProduct_bound (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ) (x : Fin n → ℕ)
    (hb : ∀ V ∈ T, ∀ t, |b x V t| ≤ 1) (z : Fin (m + 1) → ℤ) :
    |maskMultiplicativeProduct T b x z| ≤ 1 := by
  unfold maskMultiplicativeProduct
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ V ∈ T, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro V _; exact abs_nonneg _
      · intro V hV; exact hb V hV _
    _ = 1 := by simp

theorem maskUpdatedMultiplicativeMasks_bound {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (ξ : Fin (2 + n) → ℕ)
    (hb : ∀ V ∈ T, ∀ t, |b (maskFreshOldTuple ξ) V t| ≤ 1) :
    ∀ V ∈ T, ∀ t, |maskUpdatedMultiplicativeMasks P b ξ V t| ≤ 1 := by
  intro V hV t
  unfold maskUpdatedMultiplicativeMasks
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul (hb V hV _) (hb V hV _) (abs_nonneg _) zero_le_one

theorem maskUpdatedMultiplicativeMasks_support_bound {N : ℕ} (gap : ℕ → Fin N)
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U)
    (T : Finset (Finset (Fin (m + 1)))) (w : ℕ)
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (hb : ∀ x ∈ (monomialRowPrimeMass m gap n w).support, ∀ V ∈ T, ∀ t, |b x V t| ≤ 1) :
    ∀ ξ ∈ (monomialRowPrimeMass m gap (2 + n) w).support, ∀ V ∈ T, ∀ t,
      |maskUpdatedMultiplicativeMasks P b ξ V t| ≤ 1 := by
  intro ξ hξ
  exact maskUpdatedMultiplicativeMasks_bound P T b ξ
    (hb _ (maskFreshPrimeTuple_support_projections gap w ξ hξ).1)

theorem maskMultiplicativeProduct_erase (T : Finset (Finset (Fin (m + 1))))
    (U : Finset (Fin (m + 1))) (hU : U ∈ T)
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ) (x : Fin n → ℕ)
    (z : Fin (m + 1) → ℤ) :
    maskMultiplicativeProduct T b x z =
      b x U (maskCoordinateMonomial U z) * maskMultiplicativeProduct (T.erase U) b x z := by
  exact (Finset.mul_prod_erase T (fun V => b x V (maskCoordinateMonomial V z)) hU).symm

end Hindman168
