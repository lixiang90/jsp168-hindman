import Hindman168.RoughPolynomialExactDivision
import Hindman168.PowerGrowth

namespace Hindman168
open Filter Polynomial
open scoped Topology

theorem rough_interpolation_error_below_lattice {S Z C D : ℝ}
    (hS : 1 ≤ S) (hZ : S ≤ Z) (hC : 0 ≤ C) (hD : 0 < D)
    (q e : ℕ) (he : 0 < e)
    (hlarge : C * D * 3 ^ q * S ^ (2 * q + 1) < Z) :
    C * (S / Z) ^ e * (1 + 2 * S) ^ q < 1 / (D * S ^ q) := by
  have hs : 0 < S := by linarith
  have hz : 0 < Z := hs.trans_le hZ
  have hr0 : 0 ≤ S / Z := div_nonneg hs.le hz.le
  have hr1 : S / Z ≤ 1 := (div_le_one hz).mpr hZ
  have hp : (S / Z) ^ e ≤ S / Z := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr1)
  have hside : (1 + 2 * S) ^ q ≤ (3 * S) ^ q := by
    gcongr
    linarith
  have hmajor : C * (S / Z) ^ e * (1 + 2 * S) ^ q ≤ C * (S / Z) * (3 * S) ^ q := by
    gcongr
  apply hmajor.trans_lt
  apply (lt_div_iff₀ (mul_pos hD (pow_pos hs q))).mpr
  have hid : C * (S / Z) * (3 * S) ^ q * (D * S ^ q) =
      (C * D * 3 ^ q * S ^ (2 * q + 1)) / Z := by
    rw [mul_pow, pow_add, pow_mul]
    field_simp
    ring
  rw [hid]
  exact (div_lt_one hz).mpr hlarge

theorem rough_interpolation_error_eventually {α : Type*} {l : Filter α}
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 ≤ Z w)
    (C : ℝ) (hC : 0 ≤ C) (D : ℝ) (hD : 0 < D) (q e : ℕ) (he : 0 < e) :
    ∀ᶠ w in l, C * (S w / Z w) ^ e * (1 + 2 * S w) ^ q <
      1 / (D * S w ^ q) := by
  have hs0 : ∀ᶠ w in l, 0 ≤ S w := hS.mono (fun _ h => by linarith)
  have hlinear := hg.eventually_bound hZ hs0 1 (by norm_num : (0 : ℝ) < 1)
  have hlarge := hg.eventually_bound hZ hs0 (2 * q + 1)
    (by positivity : (0 : ℝ) < (C + 1) * D * 3 ^ q)
  filter_upwards [hS, hlinear, hlarge] with w hs hz hl
  apply rough_interpolation_error_below_lattice hs (by simpa using hz) hC hD q e he
  have hpos : 0 < D * 3 ^ q * S w ^ (2 * q + 1) := by positivity
  nlinarith

theorem rough_interpolation_exact_division_eventually
    {α : Type*} {l : Filter α} {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 ≤ Z w)
    (D q e : ℕ) (hD : 0 < D) (he : 0 < e) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ w in l, ∀ (R : ℚ[X]) (P : ℤ[X]) (t : ℤ) (m : ℕ),
      0 < m → (m : ℝ) ≤ S w →
      Polynomial.C (D : ℚ) * R = P.map (Int.castRingHom ℚ) → P.natDegree ≤ q → R.natDegree ≤ q →
      (∀ j < e, |(((derivative^[j] R).eval (-(t : ℚ) / m) : ℚ) : ℝ)| ≤
        C * (S w / Z w) ^ e * (1 + 2 * S w) ^ q) →
      ∃ M : ℚ[X], R = (Polynomial.C (t : ℚ) + Polynomial.C (m : ℚ) * X) ^ e * M ∧
        M.natDegree ≤ q - e := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  filter_upwards [rough_interpolation_error_eventually hg hS hZ C hC D hd q e he, hS]
    with w hw hs R P t m hm hmS hclear hP hR herr
  apply rough_small_derivatives_exact_division R P D q e hD hclear hP hR t m hm
  intro j hj
  apply (herr j hj).trans_lt (hw.trans_le _)
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

end Hindman168
