import Hindman168.UnitTorusOptionAffineSlabInverse
import Hindman168.ScalarFractionalBracketBlockFreezing
import Hindman168.DenseCompleteIntervalBlock
import Hindman168.ShortIntervalDensityBound

/-! GENUINE small-linear-slope bracket inverse: actual affine refinement,
complete dense block, SAME shifted samples, freezing and original-N recovery.
The selected coordinate is maximal; no short-block inverse is assumed. -/
namespace Hindman168
open Set
open scoped BigOperators Classical

theorem unit_torus_option_small_slope_bracket_inverse (ι : Type*) [Fintype ι]
    (Z δ A0 B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA0 : 0 ≤ A0) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (β α : ℝ) (ζ γ : Option ι → ℝ),
      (∀ i, |ζ i| ≤ Z) → (∀ i, |ζ i| ≤ |ζ none|) → ∀ N : ℕ, 0 < N → (N : ℝ)*|α| ≤ A0 →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
          (∀ i, (N : ℝ)*|ζ i| ≤ (A : ℝ)) ∨
            ∃ k : Option ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
              (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨C,hC,T0,hT0,hRelative⟩ := scalar_fractional_bracket_relative_slope (Option ι) δ A0 B hδ hδ1 hA0 hB
  obtain ⟨c,hc,K,_,hDetect⟩ := unit_torus_option_affine_slab_inverse ι Z (δ/2) hZ (by positivity) (by linarith)
  let J := ⌈4*C/c⌉₊+1
  have hJ : 0 < J := by dsimp only [J]; omega
  have hjr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hCJ : C/(J : ℝ) ≤ c/4 := by
    have hh : 4*C/c ≤ (J : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ ⌈4*C/c⌉₊)
    have hm := (div_le_iff₀ hc).mp hh
    apply (div_le_iff₀ hjr).mpr
    nlinarith
  let T := T0+J+⌈2*(J : ℝ)/δ⌉₊+1
  let P := B+4*B/c
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hBP : B ≤ P := by
    dsimp only [P]
    have hh : 0 ≤ 4*B/c := by positivity
    linarith
  have h4P : 4*B/c ≤ P := by dsimp only [P]; linarith
  let A := 2*J*K+⌈(T : ℝ)*Z⌉₊+⌈P⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have h2A : 2*J*K ≤ A := by dsimp only [A]; omega
  have hKA : K ≤ A := (Nat.le_mul_of_pos_left K (by omega : 0 < 2*J)).trans h2A
  have hPA : P ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈P⌉₊ ≤ A by dsimp only [A]; omega))
  have hTA : (T : ℝ)*Z ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈(T : ℝ)*Z⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A,hA,?_⟩
  intro β α ζ γ hζ hmax N hN hα hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hTN : T ≤ N
  · let w := |ζ none|
    have hw : 0 ≤ w := abs_nonneg _
    by_cases hsmall : (N : ℝ)*w ≤ P
    · exact Or.inl (fun i => ((mul_le_mul_of_nonneg_left (hmax i) hn.le).trans hsmall).trans hPA)
    · have hne : ζ none ≠ 0 := by
        intro hz
        apply hsmall
        simpa only [w,hz,abs_zero,mul_zero] using hP
      have hBw : B ≤ (N : ℝ)*w := hBP.trans (lt_of_not_ge hsmall).le
      have hT0N : T0 ≤ N := (show T0 ≤ T by dsimp only [T]; omega).trans hTN
      have hSlope := hRelative β α ζ γ w hw hmax N hT0N hα hBw hdense
      have hJN : J ≤ N := (show J ≤ T by dsimp only [T]; omega).trans hTN
      have hL : 0 < N/J := Nat.div_pos hJN hJ
      have htail : 2*(J : ℝ) ≤ δ*(N : ℝ) := by
        have hh : 2*(J : ℝ)/δ ≤ (N : ℝ) := (Nat.le_ceil _).trans
          (by exact_mod_cast ((show ⌈2*(J : ℝ)/δ⌉₊ ≤ T by dsimp only [T]; omega).trans hTN))
        have hm := (div_le_iff₀ hδ).mp hh
        nlinarith
      let U := (Finset.range N).filter (fun h : ℕ =>
        (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)
      obtain ⟨j,_,_,hblock⟩ := dense_complete_interval_block N J hJ hL δ hδ htail U (Finset.filter_subset _ _) hdense
      let a := j*(N/J)
      let ε := B/(N : ℝ)+C*w/(J : ℝ)
      have hBN : B/(N : ℝ) ≤ c*w/4 := by
        have hh : 4*B/c ≤ (N : ℝ)*w := h4P.trans (lt_of_not_ge hsmall).le
        have hm := (div_le_iff₀ hc).mp hh
        apply (div_le_iff₀ hn).mpr
        nlinarith
      have htol : ε ≤ c*w := by
        have hm := mul_le_mul_of_nonneg_right hCJ hw
        dsimp only [ε]
        rw [div_mul_eq_mul_div] at hm
        nlinarith
      have hsub : ((Finset.range (N/J)).filter (fun n => a+n ∈ U)) ⊆
          (Finset.range (N/J)).filter (fun n : ℕ =>
            ‖((β+α*(a : ℝ)+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) : ℝ) : UnitAddCircle)‖ ≤ ε) := by
        intro n hh
        obtain ⟨hrange,hU⟩ := Finset.mem_filter.mp hh
        have hsmall' := (Finset.mem_filter.mp hU).2
        exact Finset.mem_filter.mpr ⟨hrange,scalar_fractional_bracket_block_freezing β α ζ γ a n N J hN hJ
          (Finset.mem_range.mp hrange) B C w hSlope hsmall'⟩
      have hsize : (δ/2)*(N/J : ℕ) ≤ ((Finset.range (N/J)).filter (fun n : ℕ =>
          ‖((β+α*(a : ℝ)+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) : ℝ) : UnitAddCircle)‖ ≤ ε)).card :=
        hblock.trans (by exact_mod_cast Finset.card_le_card hsub)
      obtain ⟨k,hk,hsizeK,hphase⟩ := hDetect (β+α*(a : ℝ)) ζ γ a ε hζ hmax hne htol (N/J) hL hsize
      have hlr : (0 : ℝ) < (N/J : ℕ) := by exact_mod_cast hL
      have hratio : (N : ℝ) ≤ (2*(J : ℝ))*((N/J : ℕ) : ℝ) :=
        (div_le_iff₀ hlr).mp (shortInterval_card_ratio N J hJ hL)
      have hfinal : (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (2*J*K : ℕ) := by
        have hm := mul_le_mul_of_nonneg_right hratio (norm_nonneg (((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)))
        have hh := mul_le_mul_of_nonneg_left hphase (by positivity : 0 ≤ 2*(J : ℝ))
        push_cast
        nlinarith
      exact Or.inr ⟨k,hk,hsizeK.trans hKA,hfinal.trans (by exact_mod_cast h2A)⟩
  · have hNT : (N : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hTN))
    exact Or.inl (fun i => ((mul_le_mul_of_nonneg_left (hζ i) hn.le).trans
      (mul_le_mul_of_nonneg_right hNT hZ)).trans hTA)

end Hindman168
