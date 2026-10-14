import Hindman168.UnitCircleStrongLinearRecurrence
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open scoped Classical

theorem unit_circle_affine_offset_from_small_value (x b ε : ℝ) (N n q A : ℕ)
    (hn : n ≤ N) (hq : q ≤ A) (hε : 0 ≤ ε)
    (hsmall : ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hslope : (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ 16*(A : ℝ)*ε/δ) :
    ‖(((q : ℝ)*b : ℝ) : UnitAddCircle)‖ ≤ 17*(A : ℝ)*ε/δ := by
  have he : (q : ℝ)*b = (q : ℝ)*(b+(n : ℝ)*x)-(n : ℝ)*((q : ℝ)*x) := by ring
  rw [he, AddCircle.coe_sub]
  have hm := mod_one_natural_multiplier_norm_le q (b+(n : ℝ)*x)
  have hstep := mod_one_natural_multiplier_norm_le n ((q : ℝ)*x)
  have hqn : (q : ℝ) ≤ A := by exact_mod_cast hq
  have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hfirst : ‖(((q : ℝ)*(b+(n : ℝ)*x) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*ε :=
    hm.trans ((mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg q)).trans
      (mul_le_mul_of_nonneg_right hqn hε))
  have hsecond : ‖(((n : ℝ)*((q : ℝ)*x) : ℝ) : UnitAddCircle)‖ ≤ 16*(A : ℝ)*ε/δ :=
    hstep.trans ((mul_le_mul_of_nonneg_right hnn (norm_nonneg _)).trans hslope)
  have hadd := (norm_sub_le _ _).trans (add_le_add hfirst hsecond)
  apply hadd.trans
  apply (le_div_iff₀ hδ).mpr
  have hδε := mul_le_mul_of_nonneg_left hδ1 (mul_nonneg (Nat.cast_nonneg A) hε)
  have heq : (16*(A : ℝ)*ε/δ)*δ = 16*(A : ℝ)*ε := div_mul_cancel₀ _ hδ.ne'
  nlinarith

/-- Genuine affine scalar small-value inverse, including the constant
coefficient, with one fixed large-box threshold and error bound. -/
theorem unit_circle_affine_small_value_inverse (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ (x b : ℝ) (N : ℕ), B ≤ N → ∀ ε : ℝ,
      0 ≤ ε → ε ≤ δ/10 →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
        ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ B ∧
        (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε ∧
        ‖(((q : ℝ)*b : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_strong_linear_recurrence δ hδ hδ1
  let B := A+⌈17*(A : ℝ)/δ⌉₊+⌈8*(A : ℝ)/δ⌉₊+1
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hB : 0 < B := by dsimp only [B]; omega
  have h17 : 17*(A : ℝ)/δ ≤ B :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈17*(A : ℝ)/δ⌉₊ ≤ B by dsimp only [B]; omega))
  have h8 : 8*(A : ℝ)/δ ≤ B :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈8*(A : ℝ)/δ⌉₊ ≤ B by dsimp only [B]; omega))
  refine ⟨B, hB, ?_⟩
  intro x b N hBN ε hε hεsmall hdense
  have hN : 0 < N := lt_of_lt_of_le hB hBN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBNr : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hlarge : 8*(A : ℝ) ≤ δ*(N : ℝ) := by
    have h := (div_le_iff₀ hδ).mp (h8.trans hBNr)
    nlinarith
  obtain ⟨q, hq, hqA, hslope⟩ := hinv x b N hN ε hε hεsmall hlarge hdense
  have hsnon : ((Finset.range N).filter (fun n : ℕ =>
      ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).Nonempty := by
    apply Finset.card_pos.mp
    have hc : (0 : ℝ) < ((Finset.range N).filter (fun n : ℕ =>
      ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card :=
      lt_of_lt_of_le (mul_pos hδ hNr) hdense
    exact_mod_cast hc
  obtain ⟨n, hn⟩ := hsnon
  have hnsmall := (Finset.mem_filter.mp hn).2
  have hnN := (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
  have hoffset := unit_circle_affine_offset_from_small_value x b ε N n q A
    hnN hqA hε hnsmall δ hδ hδ1 hslope
  have h16 : 16*(A : ℝ)/δ ≤ B := by
    have hAle : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    exact (div_le_div_of_nonneg_right (by nlinarith) hδ.le).trans h17
  have h16ε : 16*(A : ℝ)*ε/δ ≤ (B : ℝ)*ε := by
    apply (div_le_iff₀ hδ).mpr
    have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp h16) hε
    nlinarith
  have h17ε : 17*(A : ℝ)*ε/δ ≤ (B : ℝ)*ε := by
    apply (div_le_iff₀ hδ).mpr
    have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp h17) hε
    nlinarith
  exact ⟨q, hq, hqA.trans hAB, hslope.trans h16ε, hoffset.trans h17ε⟩

end Hindman168
