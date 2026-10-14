import Hindman168.PolynomialNormalizedIntegerRows

/-!
All actual generated rows have integer normalization on an ordered chain.
Anchor units follow from the derived monomial certificates and pool law.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

structure PolynomialRowFamily.NormalizedIntegerRowConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (W : ℕ) : Prop where
  coefficient_cast : ∀ i k, (F.normalizedIntegerRow x c i k : ℚ) =
    ((c k : ℚ) / c (F.normalizationAnchor i)) *
      (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k) : ℚ)
  form_cast : ∀ i z, (F.normalizedIntegerLinearForm x c i z : ℚ) = F.normalizedLinearForm x c i z
  anchor : ∀ i, F.normalizedIntegerRow x c i (F.normalizationAnchor i) =
    MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i (F.normalizationAnchor i))
  off_anchor_W : ∀ i k, k ≠ F.normalizationAnchor i → (W : ℤ) ∣ F.normalizedIntegerRow x c i k

theorem PolynomialRowFamily.ordered_integer_row_conditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (W : ℕ)
    (hc : ∀ k, 0 < c k)
    (hratio : ∀ i j, i < j → c j ∣ c i ∧ W ∣ c i / c j) :
    F.NormalizedIntegerRowConditions x c W := by
  have hdiv (i : Fin r) (k : Fin (m + 1)) (hk : k ≤ F.normalizationAnchor i) :
      c (F.normalizationAnchor i) ∣ c k := by
    rcases lt_or_eq_of_le hk with hlt | rfl
    · exact (hratio _ _ hlt).1
    · exact dvd_refl _
  exact {
    coefficient_cast := fun i k => F.normalizedIntegerRow_cast x c i (hc _) (hdiv i) k
    form_cast := fun i z => F.normalizedIntegerLinearForm_cast x c i (hc _) (hdiv i) z
    anchor := fun i => F.normalizedIntegerRow_anchor x c i (hc _)
    off_anchor_W := fun i k hk => F.normalizedIntegerRow_off_anchor_W_divisible x c W i
      (fun j hj => (hratio _ _ hj).2) k hk }

theorem maskGenerated_chain_integer_row_conditions (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ x,
      (maskGeneratedRowDataFamily m gap t).rows.NormalizedIntegerRowConditions x
        (masterColumnCoefficient N a (fun w => (C w).block) w) (primorial w) := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hmem : ∀ k, a k ∈ Finset.univ.image a := fun k =>
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  filter_upwards [hF.column_coefficients a hmem (fun w => (C w).block) hC
    (fun w k => (C w).block_nonempty k), hF.chain_column_ratios a hmem C hC] with w hw hratio
  intro t x
  exact (maskGeneratedRowDataFamily m gap t).rows.ordered_integer_row_conditions x _ _
    (fun k => (hw k).1) hratio

theorem maskGenerated_chain_integer_anchor_units (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support,
      ∀ i q, 0 < q → q ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val →
        IsUnit ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor i) : ZMod q) := by
  filter_upwards [maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    maskGenerated_rows_eventually_bounded_units m gap] with w hrows hunits
  intro t x hx i q hq hcap
  rw [(hrows t x).anchor i]
  exact (hunits t x hx i _
    ((maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor_ne_zero i) q hq hcap).2

end Hindman168
