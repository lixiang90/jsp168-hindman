import Hindman168.PowerGrowth

/-! Genuine power growth gives ONE threshold for every original dyadic
step and box input. No desired coefficient bound is a growth premise. -/
namespace Hindman168
open Filter

theorem rough_original_bad_pair_scale_thresholds {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 ≤ Z w)
    (c Z0 : ℝ) (hc : 0 < c) (hZ0 : 1 ≤ Z0) :
    ∀ᶠ w in l, Z0 ≤ Z w ∧ ∀ t : ℕ, S w ≤ t → (t : ℝ) < 2*S w →
      0 < t ∧ Z0 ≤ Z w/t ∧ (t : ℝ) ≤ Z w ∧ (t : ℝ) ≤ (c/2)*Z w := by
  let R := 2*Z0+4/c+2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hLarge := hg.eventually_bound hZ (hS.mono (fun _ h => zero_le_one.trans h)) 1 hR
  filter_upwards [hLarge,hS] with w hw hs
  simp only [pow_one] at hw
  have hSpos : 0 < S w := zero_lt_one.trans_le hs
  have hRatio : 0 < 4/c := by positivity
  have hZ0pos : 0 < Z0 := zero_lt_one.trans_le hZ0
  have hRZ0 : Z0 ≤ R := by dsimp only [R]; linarith
  have hR2 : 2 ≤ R := by dsimp only [R]; linarith
  have hRc : 4/c ≤ R := by dsimp only [R]; linarith
  have hBase : R ≤ Z w := (le_mul_of_one_le_right hR.le hs).trans hw
  refine ⟨hRZ0.trans hBase,?_⟩
  intro t hlo hhi
  have htReal : (0 : ℝ) < t := hSpos.trans_le hlo
  have ht : 0 < t := by exact_mod_cast htReal
  have h2Z0S : 2*Z0*S w ≤ Z w :=
    (mul_le_mul_of_nonneg_right (by dsimp only [R]; linarith : 2*Z0 ≤ R) hSpos.le).trans hw
  have htZ0 : (t : ℝ)*Z0 ≤ Z w := by nlinarith
  have htZ : (t : ℝ) ≤ Z w := by
    have hh := (mul_le_mul_of_nonneg_right hR2 hSpos.le).trans hw
    linarith
  have hcz : (4/c)*S w ≤ Z w := (mul_le_mul_of_nonneg_right hRc hSpos.le).trans hw
  have hcMul : 4*S w ≤ c*Z w := by
    have hh := mul_le_mul_of_nonneg_left hcz hc.le
    field_simp at hh
    nlinarith
  exact ⟨ht,(le_div_iff₀ htReal).mpr (by nlinarith [htZ0]),htZ,by nlinarith⟩

end Hindman168
