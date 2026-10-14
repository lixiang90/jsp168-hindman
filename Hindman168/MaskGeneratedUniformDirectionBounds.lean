import Hindman168.PolynomialTranslationSizeBounds

/-! One direction-size exponent depends only on the number of columns. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

noncomputable def maskRowDirectionSizeExponent (m : ℕ) : ℕ :=
  Finset.univ.sup (fun t : Fin (Fintype.card (LargeColumnSubset m)) =>
    let S := (Fintype.equivFin (LargeColumnSubset m)).symm t
    (fullMaskRowStage S.val S.property).rows.translationSizeExponent
      (fullMaskRowStage S.val S.property).target)

theorem maskGenerated_direction_exponent_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    (maskGeneratedRowDataFamily m gap t).rows.translationSizeExponent
      (maskGeneratedRowDataFamily m gap t).target ≤ maskRowDirectionSizeExponent m := by
  exact Finset.le_sup (f := fun u : Fin (Fintype.card (LargeColumnSubset m)) =>
    let S := (Fintype.equivFin (LargeColumnSubset m)).symm u
    (fullMaskRowStage S.val S.property).rows.translationSizeExponent
      (fullMaskRowStage S.val S.property).target) (Finset.mem_univ t)

theorem maskGenerated_uniform_integer_translation_size_bounds (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (block : ℕ → Fin (m + 1) → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support, ∀ i k,
      (((maskGeneratedRowDataFamily m gap t).rows.integerTranslation (maskGeneratedMaster m gap)
        w (masterColumnCoefficient N a block w) x (maskGeneratedRowDataFamily m gap t).target i k).natAbs ≤
        (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
          (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ maskRowDirectionSizeExponent m) ∧
      (((maskGeneratedRowDataFamily m gap t).rows.rootIntegerTranslation (maskGeneratedMaster m gap)
        w (masterColumnCoefficient N a block w) x (maskGeneratedRowDataFamily m gap t).target k).natAbs ≤
        (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
          (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ maskRowDirectionSizeExponent m) := by
  filter_upwards [maskGenerated_integer_translation_size_bounds m gap a ha block hblock hnonempty] with w hw
  intro t x hx i k
  have hB : 1 ≤ ((maskGeneratedMaster m gap).pool w (gap w).val).upper +
      (maskGeneratedMaster m gap).auxiliary w (gap w).val := by
    have h := (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
    omega
  have hpower := Nat.pow_le_pow_right hB (maskGenerated_direction_exponent_le m gap t)
  exact ⟨(hw t x hx i k).1.trans hpower, (hw t x hx i k).2.trans hpower⟩

end Hindman168
