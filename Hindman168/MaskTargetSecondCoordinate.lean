import Hindman168.MaskTargetProgressionTransfer

/-! The actual target has another supported column before its normalization
anchor. Its normalized coefficient is a unit modulo the positive anchor
multiplier, using column-disjoint pool primes and the actual smooth ratios. -/

set_option maxHeartbeats 2000000

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

theorem normalizationAnchor_has_earlier_nonzero {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (i : Fin r)
    (hcard : 2 ≤ (F.support i).card) :
    ∃ j, j < F.normalizationAnchor i ∧ F.row i j ≠ 0 := by
  have ha : F.normalizationAnchor i ∈ F.support i := Finset.max'_mem _ _
  have hc : 0 < ((F.support i).erase (F.normalizationAnchor i)).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
  obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hj
  have hn := (Finset.mem_filter.mp hm).2
  exact ⟨j, lt_of_le_of_ne (F.le_normalizationAnchor i j hn) hne, hn⟩

end Hindman168.PolynomialRowFamily

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

theorem targetRoot_support_card_ge_two :
    2 ≤ ((maskGeneratedRowDataFamily m gap t).rows.support (maskGeneratedRowDataFamily m gap t).target).card := by
  let S := (Fintype.equivFin (LargeColumnSubset m)).symm t
  have he : (maskGeneratedRowDataFamily m gap t).rows.support (maskGeneratedRowDataFamily m gap t).target = S.val := by
    change (fullMaskRowStage S.val S.property).rows.support (fullMaskRowStage S.val S.property).target = S.val
    ext k
    simpa only [PolynomialRowFamily.support, Finset.mem_filter, Finset.mem_univ, true_and] using
      (fullMaskRowStage S.val S.property).target_support k
  rw [he]
  exact S.property

theorem targetRoot_earlier_column_exists :
    ∃ j : Fin (m + 1), j < targetRootAnchor gap t ∧
      (maskGeneratedRowDataFamily m gap t).rows.row (maskGeneratedRowDataFamily m gap t).target j ≠ 0 :=
  (maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor_has_earlier_nonzero _
    (targetRoot_support_card_ge_two gap t)

noncomputable def targetRootOtherColumn : Fin (m + 1) :=
  Classical.choose (targetRoot_earlier_column_exists gap t)

theorem targetRootOtherColumn_properties :
    targetRootOtherColumn gap t < targetRootAnchor gap t ∧
      (maskGeneratedRowDataFamily m gap t).rows.row (maskGeneratedRowDataFamily m gap t).target
        (targetRootOtherColumn gap t) ≠ 0 := Classical.choose_spec (targetRoot_earlier_column_exists gap t)

include ha hC in
theorem actual_target_off_anchor_residue_unit :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ j,
      j < targetRootAnchor gap t →
      (maskGeneratedRowDataFamily m gap t).rows.row (maskGeneratedRowDataFamily m gap t).target j ≠ 0 →
      IsUnit (((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target j : ℤ) : ZMod (targetRootMultiplier gap t x)) := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha col
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hmem : ∀ col, a col ∈ Finset.univ.image a := fun col =>
    Finset.mem_image.mpr ⟨col, Finset.mem_univ _, rfl⟩
  filter_upwards [targetRoot_arithmetic_eventually gap a ha C hC t,
    actualColumnBounds_eventually (m := m) gap a ha C hC,
    hF.chain_column_ratios a hmem C hC] with w hroot hc hratio
  intro x hx j hj hnonzero
  let F := (maskGeneratedRowDataFamily m gap t).rows
  let i := (maskGeneratedRowDataFamily m gap t).target
  let k := targetRootMultiplier gap t x
  let c := masterColumnCoefficient N a (fun w => (C w).block) w
  have hcoW : (primorial w).Coprime k := (hroot x hx).2.1
  have hcoM : ((maskGeneratedMaster m gap).modulus w : ℕ).Coprime k := by
    obtain ⟨e, he⟩ := hF.smooth_modulus w
    rw [he]
    exact hcoW.pow_left e
  have hdiv : c (targetRootAnchor gap t) ∣ c j := (hratio j _ hj).1
  have hquot : (c j / c (targetRootAnchor gap t)).Coprime k :=
    hcoM.of_dvd_left ((Nat.div_dvd_of_dvd hdiv).trans (hc j).2.1)
  have hn : F.row i (F.normalizationAnchor i) ≠ 0 := F.normalizationAnchor_ne_zero i
  have hcoP := (maskGenerated_rows_prime_arithmetic m gap t w x hx.1 hx.2 i).2
    j (targetRootAnchor gap t) (ne_of_lt hj) hnonzero hn
  have hmono := (maskGeneratedRowDataFamily_monomial m gap t i).monomial_of_ne_zero j hnonzero
  have hPunit : IsUnit ((MvPolynomial.eval (fun u => (x u : ℤ)) (F.row i j) : ℤ) : ZMod k) := by
    rw [hmono.eval_eq_natAbs x, Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hcoP
  have hqunit : IsUnit (((c j / c (targetRootAnchor gap t) : ℕ) : ℤ) : ZMod k) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hquot
  change IsUnit ((F.normalizedIntegerRow x c i j : ℤ) : ZMod k)
  unfold PolynomialRowFamily.normalizedIntegerRow
  rw [Int.cast_mul]
  exact hqunit.mul hPunit

include ha hC in
theorem actual_target_second_coordinate_unit :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      IsUnit (((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target (targetRootOtherColumn gap t) : ℤ) :
        ZMod (targetRootMultiplier gap t x)) := by
  filter_upwards [actual_target_off_anchor_residue_unit gap a ha C hC t] with w hw
  intro x hx
  exact hw x hx _ (targetRootOtherColumn_properties gap t).1 (targetRootOtherColumn_properties gap t).2

end Hindman168.MaskOriginalSampling
