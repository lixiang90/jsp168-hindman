import Hindman168.PeriodicHarmonic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Normalized harmonic W-unit laws and their residue error

The raw interval is `[X,X^2)`. Its normalizer and its positivity are proved
from the periodic estimate, with precisely `log X > W/X` as in the paper.
The normalized finite weights define an actual mathlib `PMF`, rather than
an unnormalized formal density. The residue error is the paper's `E_X(k)`.
-/

namespace Hindman168

open scoped BigOperators

def harmonicWindow (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => n.Coprime W)

noncomputable def harmonicNormalizer (X W : ℕ) : ℝ :=
  ∑ n ∈ harmonicWindow X W, (n : ℝ)⁻¹

noncomputable def harmonicWeight (X W n : ℕ) : ℝ :=
  if n ∈ harmonicWindow X W then (n : ℝ)⁻¹ / harmonicNormalizer X W else 0

noncomputable def residueProbability (X W k a : ℕ) : ℝ :=
  ∑ n ∈ (harmonicWindow X W).filter (fun n => n % k = a), harmonicWeight X W n

noncomputable def residueError (X W k : ℕ) : ℝ :=
  (W : ℝ) * (k + 1 : ℕ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X))

theorem harmonicNormalizer_error {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W) :
    |harmonicNormalizer X W - unitDensity W * Real.log X| ≤ (W.totient : ℝ) / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hAB : (X : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    rw [Nat.cast_pow]
    nlinarith
  have he : roughResidueHarmonic X (X ^ 2 : ℕ) W 1 0 = harmonicNormalizer X W := by
    simp only [roughResidueHarmonic, roughResidueWindow, harmonicNormalizer, harmonicWindow,
      Nat.ceil_natCast, Nat.mod_one, and_true]
  have hr : ((X ^ 2 : ℕ) : ℝ) / (X : ℝ) = X := by
    rw [Nat.cast_pow]
    field_simp
  have h := periodic_harmonic_error hXR hAB hW (by decide : 0 < 1)
    (by simp : W.Coprime 1) (by decide : 0 < 1)
  simpa only [he, hr, Nat.cast_one, div_one] using h

theorem unitDensity_pos {W : ℕ} (hW : 0 < W) : 0 < unitDensity W :=
  div_pos (by exact_mod_cast (Nat.totient_pos.mpr hW)) (by exact_mod_cast hW)

theorem harmonicNormalizer_lower {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W) :
    unitDensity W * (Real.log X - (W : ℝ) / X) ≤ harmonicNormalizer X W := by
  have h := (abs_le.mp (harmonicNormalizer_error hX hW)).1
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have he : unitDensity W * (Real.log X - (W : ℝ) / X) =
      unitDensity W * Real.log X - (W.totient : ℝ) / X := by
    unfold unitDensity
    field_simp
  rw [he]
  linarith

theorem harmonicNormalizer_pos {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) : 0 < harmonicNormalizer X W :=
  lt_of_lt_of_le (mul_pos (unitDensity_pos hW) (sub_pos.mpr hlog))
    (harmonicNormalizer_lower hX hW)

theorem harmonicWeight_nonneg {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (n : ℕ) :
    0 ≤ harmonicWeight X W n := by
  unfold harmonicWeight
  split_ifs
  · exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hZ.le
  · exact le_rfl

theorem harmonicWeight_sum {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) :
    (∑ n ∈ harmonicWindow X W, harmonicWeight X W n) = 1 := by
  classical
  simp only [harmonicWeight, Finset.sum_congr rfl (fun n hn => if_pos hn)]
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

/-- The actual finitely supported probability law used for a raw sample. -/
noncomputable def harmonicPMF (X W : ℕ) (hZ : 0 < harmonicNormalizer X W) : PMF ℕ :=
  PMF.ofFinset (fun n => ENNReal.ofReal (harmonicWeight X W n)) (harmonicWindow X W)
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => harmonicWeight_nonneg hZ n),
        harmonicWeight_sum hZ]
      simp)
    (by intro n hn; simp [harmonicWeight, hn])

theorem harmonicPMF_apply {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (n : ℕ) :
    harmonicPMF X W hZ n = ENNReal.ofReal (harmonicWeight X W n) := rfl

theorem harmonicPMF_support {X W : ℕ} (hX : 2 ≤ X)
    (hZ : 0 < harmonicNormalizer X W) :
    (harmonicPMF X W hZ).support = (↑(harmonicWindow X W) : Set ℕ) := by
  classical
  ext n
  rw [PMF.mem_support_iff, harmonicPMF_apply, ENNReal.ofReal_ne_zero_iff]
  by_cases hn : n ∈ harmonicWindow X W
  · have hnX := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    simp only [harmonicWeight, if_pos hn]
    exact ⟨fun _ => hn, fun _ => div_pos (inv_pos.mpr hnpos) hZ⟩
  · simp [harmonicWeight, hn]

/-- The real residue probabilities below are the coefficients of this
actual pushforward probability measure, not an auxiliary density. -/
noncomputable def harmonicResiduePMF (X W k : ℕ) (hk : 0 < k)
    (hZ : 0 < harmonicNormalizer X W) : PMF (Fin k) :=
  (harmonicPMF X W hZ).map (fun n => ⟨n % k, Nat.mod_lt n hk⟩)

theorem harmonicResiduePMF_apply {X W k : ℕ} (hk : 0 < k)
    (hZ : 0 < harmonicNormalizer X W) (a : Fin k) :
    harmonicResiduePMF X W k hk hZ a = ENNReal.ofReal (residueProbability X W k a.val) := by
  classical
  unfold harmonicResiduePMF
  rw [PMF.map_apply, tsum_eq_sum (s := harmonicWindow X W) (fun n hn => by
    simp [harmonicPMF_apply, harmonicWeight, hn])]
  have he : ∀ n : ℕ, (a = (⟨n % k, Nat.mod_lt n hk⟩ : Fin k)) ↔ n % k = a.val := by
    intro n
    rw [Fin.ext_iff]
    exact eq_comm
  simp only [he]
  rw [← Finset.sum_filter]
  simp only [harmonicPMF_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => harmonicWeight_nonneg hZ n)]
  rfl

theorem residueProbability_eq {X W k a : ℕ} :
    residueProbability X W k a =
      roughResidueHarmonic X (X ^ 2 : ℕ) W k a / harmonicNormalizer X W := by
  classical
  have he : (harmonicWindow X W).filter (fun n => n % k = a) =
      roughResidueWindow X (X ^ 2 : ℕ) W k a := by
    ext n
    simp only [harmonicWindow, roughResidueWindow, Nat.ceil_natCast, Finset.mem_filter,
      Finset.mem_Ico, and_assoc]
  unfold residueProbability
  have hw : ∀ n ∈ (harmonicWindow X W).filter (fun n => n % k = a),
      harmonicWeight X W n = (n : ℝ)⁻¹ / harmonicNormalizer X W := by
    intro n hn
    exact if_pos (Finset.mem_filter.mp hn).1
  rw [Finset.sum_congr rfl hw, ← Finset.sum_div, he]
  rfl

/-- Paper, equation `harmonic-residue-error`. In particular, the numerator
has `k+1`, accounting for both the class error and the normalizer error. -/
theorem harmonic_residue_error {X W k a : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hco : W.Coprime k) (ha : a < k)
    (hlog : (W : ℝ) / X < Real.log X) :
    |(k : ℝ) * residueProbability X W k a - 1| ≤ residueError X W k := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hφ : (0 : ℝ) < W.totient := by exact_mod_cast (Nat.totient_pos.mpr hW)
  have hD : 0 < Real.log X - (W : ℝ) / X := sub_pos.mpr hlog
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hZlower := harmonicNormalizer_lower hX hW
  have hAB : (X : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    rw [Nat.cast_pow]
    nlinarith
  have hr : ((X ^ 2 : ℕ) : ℝ) / (X : ℝ) = X := by rw [Nat.cast_pow]; field_simp
  have hres := periodic_harmonic_error hXR hAB hW hk hco ha
  rw [hr] at hres
  have hnorm := harmonicNormalizer_error hX hW
  let H := roughResidueHarmonic X (X ^ 2 : ℕ) W k a
  let Z := harmonicNormalizer X W
  let C := unitDensity W * Real.log X
  have hnum : |(k : ℝ) * H - Z| ≤ (W.totient : ℝ) * (k + 1 : ℕ) / X := by
    have he : (k : ℝ) * H - Z =
        (k : ℝ) * (H - unitDensity W / k * Real.log X) - (Z - C) := by
      dsimp [C]
      field_simp
      ring
    rw [he]
    have htri : |(k : ℝ) * (H - unitDensity W / k * Real.log X) - (Z - C)| ≤
        |(k : ℝ) * (H - unitDensity W / k * Real.log X)| + |Z - C| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((k : ℝ) * (H - unitDensity W / k * Real.log X)) (-(Z - C))
    rw [abs_mul, abs_of_pos hkR] at htri
    have hmul := mul_le_mul_of_nonneg_left hres hkR.le
    have hn : |Z - C| ≤ (W.totient : ℝ) / X := hnorm
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
    rw [hcast]
    simp only [div_eq_mul_inv] at htri hmul hn ⊢
    nlinarith
  have he : |(k : ℝ) * residueProbability X W k a - 1| = |(k : ℝ) * H - Z| / Z := by
    rw [residueProbability_eq]
    have he' : (k : ℝ) * H / Z - 1 = ((k : ℝ) * H - Z) / Z := by
      field_simp [show Z ≠ 0 from hZ.ne']
    rw [← mul_div_assoc, he', abs_div, abs_of_pos hZ]
  rw [he]
  calc
    |(k : ℝ) * H - Z| / Z ≤ ((W.totient : ℝ) * (k + 1 : ℕ) / X) / Z :=
      div_le_div_of_nonneg_right hnum hZ.le
    _ ≤ ((W.totient : ℝ) * (k + 1 : ℕ) / X) /
        (unitDensity W * (Real.log X - (W : ℝ) / X)) :=
      div_le_div_of_nonneg_left (by
        apply div_nonneg
        · exact mul_nonneg hφ.le (Nat.cast_nonneg _)
        · exact hXR.le) (mul_pos (unitDensity_pos hW) hD) hZlower
    _ = residueError X W k := by
      unfold residueError unitDensity
      field_simp

/-- The same `E_X(k)` bounds the total-mass distance of the entire residue
law from uniform. Probability total variation is half this quantity. -/
theorem harmonic_residue_total_mass_error {X W k : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hco : W.Coprime k) (hlog : (W : ℝ) / X < Real.log X) :
    (∑ a : Fin k, |residueProbability X W k a.val - (k : ℝ)⁻¹|) ≤ residueError X W k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hclass (a : Fin k) :
      |residueProbability X W k a.val - (k : ℝ)⁻¹| ≤ residueError X W k / k := by
    have he : residueProbability X W k a.val - (k : ℝ)⁻¹ =
        ((k : ℝ) * residueProbability X W k a.val - 1) / k := by field_simp
    rw [he, abs_div, abs_of_pos hkR]
    exact div_le_div_of_nonneg_right (harmonic_residue_error hX hW hk hco a.is_lt hlog) hkR.le
  calc
    (∑ a : Fin k, |residueProbability X W k a.val - (k : ℝ)⁻¹|) ≤
        ∑ _a : Fin k, residueError X W k / k := Finset.sum_le_sum (fun a _ => hclass a)
    _ = residueError X W k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end Hindman168
