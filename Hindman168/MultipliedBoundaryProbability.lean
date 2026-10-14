import Hindman168.MultipliedBoundaryResidues
import Hindman168.FiniteEventComparison

/-! Original pivot probabilities for a boundary of the actual product t*p.
The common period is W*H in p, so the endpoint error has no extra factor t.
Only coprimality with W, never with H, enters the count. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem rawMass_multipliedBoundary_formula (X W t H B : ℕ) (hW : 0 < W) (hH : 0 < H) :
    event (rawMass X W) (fun p => ¬ intervalInteriorRoot H B ((t * p : ℕ) : ℤ)) =
      periodicResidueHarmonic X (X ^ 2 : ℕ) (W * H) (multipliedBoundaryResidues W t H B) /
        harmonicNormalizer X W := by
  trans expectation (rawMass X W)
    (fun p => if p % (W * H) ∈ multipliedBoundaryResidues W t H B then 1 else 0)
  · rw [event_eq_expectation]
    apply expectation_congr_support
    intro p hp
    have hc : p.Coprime W := (Finset.mem_filter.mp
      (((intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset) hp)).2
    by_cases hb : intervalInteriorRoot H B ((t * p : ℕ) : ℤ)
    · have hn : p % (W * H) ∉ multipliedBoundaryResidues W t H B := by
        intro hh
        exact ((multipliedBoundaryResidues_mem_mod W t H B p hW hH).mp hh).2 hb
      simp only [hb, not_true_eq_false, if_false, hn]
    · have hy := (multipliedBoundaryResidues_mem_mod W t H B p hW hH).mpr ⟨hc, hb⟩
      simp only [hb, not_false_eq_true, if_true, hy]
  · simpa only [one_mul] using rawMass_periodic_test X W (W * H)
      (multipliedBoundaryResidues W t H B) 1
      (fun p hp => ((multipliedBoundaryResidues_mem_mod W t H B p hW hH).mp hp).1)


theorem rawMass_multipliedBoundary_bound {X W t H B d : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (ht : 0 < t) (hH : 0 < H)
    (hco : W.Coprime t) (hB : B ≤ d * H)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    event (rawMass X W) (fun p => ¬ intervalInteriorRoot H B ((t * p : ℕ) : ℤ)) ≤
      4 * (B : ℝ) / H + (4 + 8 * (d : ℝ)) * (W * t : ℕ) / H +
        (W : ℝ) * ((H : ℝ) + 1) / X := by
  let V := multipliedBoundaryResidues W t H B
  have hdim := multipliedBoundaryResidues_card_bound hW ht hH hco hB
  have htotal := multipliedBoundaryResidues_card_total (H := H) (B := B) hW ht hco
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hXX : (X : ℝ) < (X ^ 2 : ℕ) := by
    rw [Nat.cast_pow]
    have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hxratio : ((X ^ 2 : ℕ) : ℝ) / X = X := by rw [Nat.cast_pow]; field_simp
  have hh := (abs_le.mp (periodicResidueHarmonic_error hXR hXX (Nat.mul_pos hW hH)
    V (multipliedBoundaryResidues_subset W t H B))).2
  rw [hxratio] at hh
  have hmain := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdim (Nat.cast_nonneg (W * H) : (0 : ℝ) ≤ (W * H : ℕ)))
    (by linarith : 0 ≤ Real.log (X : ℝ))
  have herr := div_le_div_of_nonneg_right htotal hXR.le
  have hnum : periodicResidueHarmonic X (X ^ 2 : ℕ) (W * H) V ≤
      ((W.totient : ℝ) * (2 * B + (W * t : ℕ) * (2 + 4 * (d : ℝ)))) /
        (W * H : ℕ) * Real.log X + ((W.totient : ℝ) * ((H : ℝ) + 1)) / X := by
    dsimp [V] at hh
    linarith
  let a : ℝ := 2 * (B : ℝ) / H + (2 + 4 * (d : ℝ)) * (W * t : ℕ) / H
  let b : ℝ := (W : ℝ) * ((H : ℝ) + 1) / X
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have halg : ((W.totient : ℝ) * (2 * B + (W * t : ℕ) * (2 + 4 * (d : ℝ)))) /
      (W * H : ℕ) * Real.log X + ((W.totient : ℝ) * ((H : ℝ) + 1)) / X =
      unitDensity W * Real.log X * a + unitDensity W * b := by
    dsimp [a, b, unitDensity]
    push_cast
    field_simp
  rw [halg] at hnum
  obtain ⟨hZ, hZ1, hZlog⟩ := harmonicNormalizer_boundary_lower hX hW hlog hWX
  have hm := add_le_add (mul_le_mul_of_nonneg_right hZlog ha) (mul_le_mul_of_nonneg_right hZ1 hb)
  have hbound : periodicResidueHarmonic X (X ^ 2 : ℕ) (W * H) V ≤
      (2 * a + b) * harmonicNormalizer X W := by nlinarith
  rw [rawMass_multipliedBoundary_formula X W t H B hW hH]
  have hr := (div_le_iff₀ hZ).mpr hbound
  have he : 2 * a + b = 4 * (B : ℝ) / H + (4 + 8 * (d : ℝ)) * (W * t : ℕ) / H +
      (W : ℝ) * ((H : ℝ) + 1) / X := by dsimp [a, b]; ring
  exact hr.trans_eq he

end Hindman168
