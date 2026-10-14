import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# A quantitative finite coloring for multiplicative separation

This module contains only elementary separation lemmas. It does not prove
`FiniteConjecture` or claim that the analytic core of the paper is complete.
The log-log coloring argument was developed in the current audit of the
September 23 OpenAI statement; no competing repository proof is copied here.
-/

namespace Hindman168

/-- A real interval of length strictly between one and `K - 1` cannot have
endpoint floors congruent modulo `K`. Integer floors also handle negative inputs. -/
theorem floor_emod_ne_of_gap {x y : ℝ} {K : ℤ}
    (hlower : 1 < y - x) (hupper : y - x + 1 < K) :
    Int.floor y % K ≠ Int.floor x % K := by
  intro heq
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  have hpos : 0 < Int.floor y - Int.floor x := by
    exact_mod_cast (show (0 : ℝ) < (Int.floor y : ℝ) - (Int.floor x : ℝ) by linarith)
  have hlt : Int.floor y - Int.floor x < K := by
    exact_mod_cast (show (Int.floor y : ℝ) - (Int.floor x : ℝ) < K by linarith)
  have hdiv : K ∣ Int.floor y - Int.floor x := by
    exact Int.ModEq.dvd heq.symm
  have := Int.le_of_dvd hpos hdiv
  omega

/-- On positive inputs the log-log increment is the logarithm of the ratio
of their logarithms. -/
theorem loglog_mul_sub {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Real.log (Real.log (a * b)) - Real.log (Real.log b) =
      Real.log (1 + Real.log a / Real.log b) := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hab : 1 < a * b := by nlinarith
  rw [← Real.log_div (ne_of_gt (Real.log_pos hab)) (ne_of_gt hlb),
    Real.log_mul (by linarith) (by linarith)]
  congr 1
  field_simp
  ring

/-- The increment has uniform positive lower and upper bounds if the
larger factor is at most a fixed power of the smaller. -/
theorem loglog_mul_gap {a b E : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hE : 0 < E) (hpow : b ≤ a ^ E) :
    Real.log (1 + 1 / E) ≤
        Real.log (Real.log (a * b)) - Real.log (Real.log b) ∧
    Real.log (Real.log (a * b)) - Real.log (Real.log b) ≤ Real.log 2 := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hp : Real.log b ≤ E * Real.log a := by
    have h := Real.log_le_log (by linarith : 0 < b) hpow
    simpa [Real.log_rpow (by linarith : 0 < a)] using h
  rw [loglog_mul_sub ha hb]
  constructor
  · apply Real.log_le_log (by positivity)
    have hrat : 1 / E ≤ Real.log a / Real.log b := by
      apply (div_le_div_iff₀ hE hlb).2
      nlinarith
    linarith
  · apply Real.log_le_log (by positivity)
    have hrat : Real.log a / Real.log b ≤ 1 := (div_le_one hlb).2 hlogs
    linarith

/-- A finite auxiliary coloring forces any two positive factors appearing
in one monochromatic finite-products witness to be power-separated. -/
theorem exists_power_separating_coloring (E : ℝ) (hE : 0 < E) :
    ∃ K : ℕ, ∃ χ : ℕ → Fin K, ∀ a b : ℕ,
      1 < a → a ≤ b → χ (a * b) = χ b → (a : ℝ) ^ E < b := by
  let L : ℝ := Real.log (1 + 1 / E)
  have hL : 0 < L := Real.log_pos (by have := one_div_pos.mpr hE; linarith)
  let C : ℝ := 2 / L
  have hC : 0 < C := div_pos (by norm_num) hL
  have hCL : C * L = 2 := by dsimp [C]; field_simp
  obtain ⟨K, hK⟩ := exists_nat_gt (C * Real.log 2 + 1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by have := mul_pos hC hlog2; linarith)
  have hKint : (0 : ℤ) < K := by exact_mod_cast hKpos
  let f : ℕ → ℤ := fun n => Int.floor (C * Real.log (Real.log (n : ℝ)))
  let χ : ℕ → Fin K := fun n => ⟨(f n % (K : ℤ)).toNat,
    (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hKint))).2
      (Int.emod_lt_of_pos _ hKint)⟩
  refine ⟨K, χ, ?_⟩
  intro a b ha hab heq
  by_contra hnot
  have hpow : (b : ℝ) ≤ (a : ℝ) ^ E := le_of_not_gt hnot
  have har : (1 : ℝ) < a := by exact_mod_cast ha
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨hlo, hhi⟩ := loglog_mul_gap har habr hE hpow
  have hfloor : f (a * b) % (K : ℤ) ≠ f b % (K : ℤ) := by
    apply floor_emod_ne_of_gap
    · push_cast
      have h := mul_le_mul_of_nonneg_left hlo hC.le
      dsimp [L] at hCL
      nlinarith
    · push_cast
      have h := mul_le_mul_of_nonneg_left hhi hC.le
      nlinarith
  apply hfloor
  have hv := congrArg Fin.val heq
  have hv' := congrArg (fun n : ℕ => (n : ℤ)) hv
  simpa [χ, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hKint))] using hv'

end Hindman168
