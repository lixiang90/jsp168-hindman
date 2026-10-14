import Hindman168.HarmonicDilation

/-!
# Harmonic translation, retaining the paper's original constant

For a nonnegative shift H divisible by W, the deficit of the shifted raw
law is exactly the original mass below X+H. Equal total masses imply that
the L1 distance is twice this deficit. Complete W-periods count exactly,
including when the boundary interval extends beyond the original support.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def shiftedNatMass (X W H : ℕ) : FiniteMass.Mass ℕ :=
  (rawMass X W).mapDomain (fun n => n + H)

noncomputable def translationBoundaryMass (X W H : ℕ) : FiniteMass.Mass ℕ :=
  (rawMass X W).filter (fun n => n < X + H)

theorem shiftedNatMass_apply_of_le (X W H n : ℕ) (hn : H ≤ n) :
    shiftedNatMass X W H n = harmonicWeight X W (n - H) := by
  unfold shiftedNatMass
  rw [show n = (n - H) + H from (Nat.sub_add_cancel hn).symm,
    Finsupp.mapDomain_apply (f := fun m : ℕ => m + H) (fun _ _ h => Nat.add_right_cancel h),
    rawMass_apply]
  simp only [Nat.add_sub_cancel]

theorem shiftedNatMass_apply_of_lt (X W H n : ℕ) (hn : n < H) :
    shiftedNatMass X W H n = 0 := by
  unfold shiftedNatMass
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, rfl⟩
  dsimp at hn
  omega

theorem shiftedNatMass_nonneg {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (H n : ℕ) :
    0 ≤ shiftedNatMass X W H n := by
  rcases le_or_gt H n with hn | hn
  · rw [shiftedNatMass_apply_of_le X W H n hn]
    exact harmonicWeight_nonneg hZ _
  · rw [shiftedNatMass_apply_of_lt X W H n hn]

theorem translationBoundaryMass_apply (X W H n : ℕ) :
    translationBoundaryMass X W H n = if n < X + H then harmonicWeight X W n else 0 := by
  simp only [translationBoundaryMass, Finsupp.filter_apply, rawMass_apply]

theorem shiftedNatMass_zero_below (X W H n : ℕ) (hn : n < X + H) :
    shiftedNatMass X W H n = 0 := by
  rcases le_or_gt H n with hHn | hnH
  · rw [shiftedNatMass_apply_of_le X W H n hHn]
    have hm : n - H ∉ harmonicWindow X W := by
      intro hm
      have hlow := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
      omega
    exact if_neg hm
  · exact shiftedNatMass_apply_of_lt X W H n hnH

theorem harmonicWeight_le_shifted {X W H n : ℕ} (hX : 2 ≤ X)
    (hZ : 0 < harmonicNormalizer X W) (hWH : W ∣ H) (hn : X + H ≤ n) :
    harmonicWeight X W n ≤ shiftedNatMass X W H n := by
  have hHn : H ≤ n := by omega
  rw [shiftedNatMass_apply_of_le X W H n hHn]
  by_cases hmem : n ∈ harmonicWindow X W
  · have hnI := Finset.mem_Ico.mp (Finset.mem_filter.mp hmem).1
    have hcop := (Finset.mem_filter.mp hmem).2
    have hsubcop : (n - H).Coprime W := by
      have he : n = (n - H) + H := (Nat.sub_add_cancel hHn).symm
      rw [he, Nat.coprime_comm, Nat.coprime_add_iff_left hWH] at hcop
      exact hcop.symm
    have hsubmem : n - H ∈ harmonicWindow X W :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hsubcop⟩
    have hsubpos : (0 : ℝ) < ((n - H : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - H)
    have hle : ((n - H : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n H)
    rw [harmonicWeight, if_pos hmem, harmonicWeight, if_pos hsubmem]
    apply div_le_div_of_nonneg_right _ hZ.le
    simpa only [one_div] using one_div_le_one_div_of_le hsubpos hle
  · rw [harmonicWeight, if_neg hmem]
    exact harmonicWeight_nonneg hZ _

/-- The negative part of shifted minus original is precisely the lower boundary. -/
theorem harmonic_translation_boundary {X W H : ℕ} (hX : 2 ≤ X)
    (hZ : 0 < harmonicNormalizer X W) (hWH : W ∣ H) :
    FiniteMass.distance (shiftedNatMass X W H) (rawMass X W) =
      2 * FiniteMass.total (translationBoundaryMass X W H) := by
  apply FiniteMass.distance_eq_twice_deficit
  · exact FiniteMass.total_push _ _
  · intro n
    rw [translationBoundaryMass_apply, rawMass_apply]
    by_cases hn : n < X + H
    · rw [shiftedNatMass_zero_below X W H n hn, if_pos hn]
      rw [zero_sub, abs_neg, abs_of_nonneg (harmonicWeight_nonneg hZ n)]
      ring
    · rw [if_neg hn, abs_of_nonneg (sub_nonneg.mpr
        (harmonicWeight_le_shifted hX hZ hWH (le_of_not_gt hn)))]
      ring

/-- Any interval of t complete W-periods contains exactly t*phi(W) units. -/
theorem coprime_interval_card_periods (X W t : ℕ) :
    ((Finset.Ico X (X + W * t)).filter (fun n => W.Coprime n)).card = t * W.totient := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : X + W * (t + 1) = (X + W * t) + W := by ring
    have hs := Finset.Ico_union_Ico_eq_Ico
      (Nat.le_add_right X (W * t)) (Nat.le_add_right (X + W * t) W)
    have hd : Disjoint ((Finset.Ico X (X + W * t)).filter (fun n => W.Coprime n))
        ((Finset.Ico (X + W * t) ((X + W * t) + W)).filter (fun n => W.Coprime n)) :=
      (Finset.Ico_disjoint_Ico_consecutive X (X + W * t) ((X + W * t) + W)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [he, ← hs, Finset.filter_union, Finset.card_union_of_disjoint hd, ih,
      Nat.filter_coprime_Ico_eq_totient]
    ring

theorem unitInterval_card_multiple {X W H : ℕ} (hW : 0 < W) (hWH : W ∣ H) :
    ((unitInterval X (X + H : ℕ) W).card : ℝ) = unitDensity W * H := by
  obtain ⟨t, rfl⟩ := hWH
  have he : unitInterval X (X + W * t : ℕ) W =
      (Finset.Ico X (X + W * t)).filter (fun n => W.Coprime n) := by
    simp only [unitInterval, Nat.ceil_natCast]
    congr 1
    funext n
    exact propext Nat.coprime_comm
  rw [he, coprime_interval_card_periods]
  unfold unitDensity
  simp only [Nat.cast_mul]
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  field_simp

theorem translationBoundaryMass_support (X W H : ℕ) :
    (translationBoundaryMass X W H).support ⊆ unitInterval X (X + H : ℕ) W := by
  intro n hn
  have hnz := Finsupp.mem_support_iff.mp hn
  rw [translationBoundaryMass_apply] at hnz
  split_ifs at hnz with hnupper
  · have hraw : n ∈ harmonicWindow X W := by
      by_contra ho
      simp only [harmonicWeight, if_neg ho, ne_eq, not_true_eq_false] at hnz
    have hnlow := (Finset.mem_Ico.mp (Finset.mem_filter.mp hraw).1).1
    rw [mem_unitInterval]
    exact ⟨by exact_mod_cast hnlow, by exact_mod_cast hnupper, (Finset.mem_filter.mp hraw).2⟩
  · exact (hnz rfl).elim

/-- This bound holds also for shifts larger than the original window. -/
theorem translationBoundaryMass_upper {X W H : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hZ : 0 < harmonicNormalizer X W) (hWH : W ∣ H) :
    FiniteMass.total (translationBoundaryMass X W H) ≤
      unitDensity W * H / ((X : ℝ) * harmonicNormalizer X W) := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  rw [FiniteMass.total_eq_sum _ (translationBoundaryMass_support X W H)]
  calc
    _ ≤ ∑ _n ∈ unitInterval X (X + H : ℕ) W, (X : ℝ)⁻¹ / harmonicNormalizer X W := by
      apply Finset.sum_le_sum
      intro n hn
      have hm := mem_unitInterval.mp hn
      have hnupper : n < X + H := by exact_mod_cast hm.2.1
      rw [translationBoundaryMass_apply, if_pos hnupper]
      by_cases hr : n ∈ harmonicWindow X W
      · rw [harmonicWeight, if_pos hr]
        apply div_le_div_of_nonneg_right _ hZ.le
        simpa only [one_div] using one_div_le_one_div_of_le hXR hm.1
      · rw [harmonicWeight, if_neg hr]
        exact div_nonneg (inv_nonneg.mpr hXR.le) hZ.le
    _ = unitDensity W * H / ((X : ℝ) * harmonicNormalizer X W) := by
      rw [Finset.sum_const, nsmul_eq_mul, unitInterval_card_multiple hW hWH]
      field_simp

theorem harmonic_translation_linear {X W H : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) (hWH : W ∣ H) :
    FiniteMass.distance (shiftedNatMass X W H) (rawMass X W) ≤
      2 * (H : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hθ := unitDensity_pos hW
  have hD := sub_pos.mpr hlog
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hZlower := harmonicNormalizer_lower hX hW
  rw [harmonic_translation_boundary hX hZ hWH]
  calc
    _ ≤ 2 * (unitDensity W * H / ((X : ℝ) * harmonicNormalizer X W)) :=
      mul_le_mul_of_nonneg_left (translationBoundaryMass_upper hX hW hZ hWH) (by norm_num)
    _ ≤ 2 * (unitDensity W * H /
        ((X : ℝ) * (unitDensity W * (Real.log X - (W : ℝ) / X)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (mul_nonneg hθ.le (Nat.cast_nonneg H))
        (mul_pos hXR (mul_pos hθ hD)) (mul_le_mul_of_nonneg_left hZlower hXR.le)
    _ = 2 * (H : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
      field_simp [hθ.ne']

theorem harmonic_translation_two {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (H : ℕ) :
    FiniteMass.distance (shiftedNatMass X W H) (rawMass X W) ≤ 2 := by
  have hl := FiniteMass.distance_le_totals (shiftedNatMass X W H) (rawMass X W)
    (shiftedNatMass_nonneg hZ H) (fun n => by rw [rawMass_apply]; exact harmonicWeight_nonneg hZ n)
  rw [shiftedNatMass, FiniteMass.total_push, rawMass_total hZ] at hl
  norm_num at hl
  exact hl

theorem harmonic_translation_error {X W H : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) (hWH : W ∣ H) :
    FiniteMass.distance (shiftedNatMass X W H) (rawMass X W) ≤
      min 2 (2 * (H : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X))) :=
  le_min (harmonic_translation_two (harmonicNormalizer_pos hX hW hlog) H)
    (harmonic_translation_linear hX hW hlog hWH)

theorem integer_positive_translation_commutes (X W H : ℕ) :
    (integerMass X W).mapDomain (fun z => z + (H : ℤ)) =
      (shiftedNatMass X W H).mapDomain (fun n : ℕ => (n : ℤ)) := by
  unfold integerMass shiftedNatMass
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  have hf : (fun z : ℤ => z + (H : ℤ)) ∘ (fun n : ℕ => (n : ℤ)) =
      (fun n : ℕ => (n : ℤ)) ∘ (fun n : ℕ => n + H) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add]
  rw [hf]

theorem integer_positive_translation_distance (X W H : ℕ) :
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => z + (H : ℤ))) (integerMass X W) =
      FiniteMass.distance (shiftedNatMass X W H) (rawMass X W) := by
  rw [integer_positive_translation_commutes, integerMass,
    FiniteMass.distance_push_injective (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective]

theorem integer_translation_distance_natAbs (X W : ℕ) (h : ℤ) :
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => z + h)) (integerMass X W) =
      FiniteMass.distance (shiftedNatMass X W h.natAbs) (rawMass X W) := by
  let f := fun h : ℤ =>
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => z + h)) (integerMass X W)
  change f h = _
  rcases (Int.natAbs_eq_iff.mp (rfl : h.natAbs = h.natAbs)) with he | he
  · exact (congrArg f he).trans (integer_positive_translation_distance X W h.natAbs)
  · exact (congrArg f he).trans
      ((FiniteMass.translation_distance_neg (integerMass X W) (h.natAbs : ℤ)).trans
        (integer_positive_translation_distance X W h.natAbs))

/-- Paper's harmonic-translation estimate for arbitrary signed W-multiples. -/
theorem integer_harmonic_translation_error {X W : ℕ} {h : ℤ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) (hWh : (W : ℤ) ∣ h) :
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => z + h)) (integerMass X W) ≤
      min 2 (2 * |(h : ℝ)| / ((X : ℝ) * (Real.log X - (W : ℝ) / X))) := by
  rw [integer_translation_distance_natAbs]
  have hWH : W ∣ h.natAbs := Int.ofNat_dvd_left.mp hWh
  have hAbs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simpa only [hAbs] using harmonic_translation_error hX hW hlog hWH

end Hindman168
