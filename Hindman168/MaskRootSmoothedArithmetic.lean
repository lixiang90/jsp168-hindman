import Hindman168.PolynomialRootSmoothedRows
import Hindman168.MaskOriginalAdditiveData
import Hindman168.MaskCopiedUniformBounds

/-! Arithmetic certificates for the actual root-smoothed mask family on
original good tuples. Primitivity, independence and fixed m-only dimensions
are derived, without assuming these conclusions as sampling conditions. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

abbrev MaskRootCopiedRow (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  PolynomialRowFamily.RootSmoothedCopy (maskGeneratedRowDataFamily m gap t).target

abbrev MaskRootCopiedIndex (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  Fin (Fintype.card (PolynomialRowFamily.RootSmoothedColumn
    (maskGeneratedRowDataFamily m gap t).target m))

noncomputable def maskRootCopiedCoefficient (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (i : MaskRootCopiedRow m gap t) (j : MaskRootCopiedIndex m gap t) : ℤ :=
  (maskGeneratedRowDataFamily m gap t).rows.rootSmoothedFinIntegerCoefficient
    (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
    (maskGeneratedRowDataFamily m gap t).target i j

theorem maskRootCopiedRow_card_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Fintype.card (MaskRootCopiedRow m gap t) ≤
      2 * ((maskRowCountBound m + 1) * 2 ^ maskRowCountBound m) := by
  exact (rootSmoothedAdditiveCopy_card_le _).trans
    (Nat.mul_le_mul_left 2 (maskCopiedRow_card_le m gap t))

theorem maskRootCopiedColumn_card_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Fintype.card (MaskRootCopiedIndex m gap t) ≤ (m + 1) + 2 * maskRowCountBound m + 2 := by
  rw [Fintype.card_fin, rootSmoothedAdditiveColumn_card]
  have h := maskGenerated_additive_dimension_le m gap t
  omega

theorem maskRootCopiedCoefficient_primitive_eventually (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ p : ℕ, p.Prime → p ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val →
        ∀ i : MaskRootCopiedRow m gap t,
          ∃ j, (maskRootCopiedCoefficient m gap a C t w x i j : ZMod p) ≠ 0 := by
  filter_upwards [maskGenerated_chain_integer_row_directions m gap a ha C hC] with w hd
  intro x hx p hp hpV i
  have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support := hx.1
  exact (maskGeneratedRowDataFamily m gap t).rows.rootSmoothedFinIntegerCoefficient_primitive
    (maskGeneratedMaster m gap) w _ x _ (hd t x hpool hx.2) p hp hpV i

theorem maskRootCopiedCoefficient_pair_independent_eventually (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ p : ℕ, p.Prime → w < p → p ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val →
        (∀ f ∈ (maskGeneratedRowDataFamily m gap t).rows.catalog
          (maskGeneratedRowDataFamily m gap t).target,
          MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) →
        ∀ i j : MaskRootCopiedRow m gap t, i ≠ j →
          LinearIndependent (ZMod p)
            ![(fun k => (maskRootCopiedCoefficient m gap a C t w x i k : ZMod p)),
              (fun k => (maskRootCopiedCoefficient m gap a C t w x j k : ZMod p))] := by
  filter_upwards [maskGenerated_chain_integer_row_directions m gap a ha C hC,
    maskGenerated_additive_elimination_data m gap a ha C hC] with w hd he
  intro x hx p hp hwp hpV havoid i j hij
  have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support := hx.1
  obtain ⟨H⟩ := he t x hx.2
  exact PolynomialRowFamily.rootSmoothedFinIntegerCoefficient_pair_independent H
    (hd t x hpool hx.2) p hp hwp hpV havoid i j hij

end Hindman168
