import Hindman168.PolynomialSmallValueNaturalMultiples
import Hindman168.PolynomialSmallValueRescale
import Hindman168.FiniteBoundedCandidateDensity

namespace Hindman168
open Polynomial
open scoped Classical

/-- Genuine uniform positive-tolerance polynomial small-value inverse for
all nonconstant coefficients on sufficiently long ORIGINAL intervals.
Actual natural multiples, actual candidate density and true recurrence
produce the multipliers; no small-value inverse is assumed. -/
theorem polynomial_small_values_positive_nonconstant (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ S T : ℕ, ∃ C : ℝ, 0 < S ∧ 0 < T ∧ 0 < C ∧
      ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, T ≤ N → ∀ ε : ℝ,
        0 < ε → ε ≤ δ/10 →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ S ∧ ∀ i : ℕ, 0 < i → i ≤ D →
          (N : ℝ)^i*‖(((Q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ C*ε := by
  obtain ⟨B, hB, hcoarse⟩ := unit_circle_polynomial_small_values_coarse_inverse D δ hδ hδ1
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let μ := 1/(B : ℝ)
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hμ1 : μ ≤ 1 := by dsimp only [μ]; exact (div_le_one hBr).mpr hB1
  obtain ⟨K, hK, hrec⟩ := unit_circle_strong_linear_recurrence μ hμ hμ1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let W := ⌈8*(K : ℝ)/μ⌉₊+1
  let ε₀ := δ/(20*((W : ℝ)+1))
  let Csmall := 320*(K : ℝ)*(B : ℝ)/(μ*δ)
  let C := (B : ℝ)/ε₀+(K : ℝ)^(D+1)*Csmall+1
  let T := ⌈10*(B : ℝ)/μ⌉₊+1
  let S := K^(D+1)*B+B+1
  have hW : 0 < W := by dsimp only [W]; omega
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hCsmall : 0 < Csmall := by dsimp only [Csmall]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hT : 0 < T := by dsimp only [T]; omega
  have hS : 0 < S := by dsimp only [S]; omega
  have hCbig : (B : ℝ)/ε₀ ≤ C := by
    have hh : 0 ≤ (K : ℝ)^(D+1)*Csmall := by positivity
    dsimp only [C]
    linarith
  have hCsm : (K : ℝ)^(D+1)*Csmall ≤ C := by
    have hh : 0 ≤ (B : ℝ)/ε₀ := by positivity
    dsimp only [C]
    linarith
  have hTbound : 10*(B : ℝ)/μ ≤ T := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈10*(B : ℝ)/μ⌉₊ ≤ T by dsimp only [T]; omega))
  have hWbound : 8*(K : ℝ)/μ ≤ W := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈8*(K : ℝ)/μ⌉₊ ≤ W by dsimp only [W]; omega))
  refine ⟨S, T, C, hS, hT, hC, ?_⟩
  intro p hp N hTN ε hε hεsmall hdense
  have hN : 0 < N := hT.trans_le hTN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hlargeε : ε₀ ≤ ε
  · obtain ⟨q, hq, hqB, hcoeff⟩ := hcoarse p hp N hN ε hεsmall hdense
    refine ⟨q, hq, hqB.trans (by dsimp only [S]; omega), ?_⟩
    intro i hi hiD
    have hb := mul_le_mul_of_nonneg_left hlargeε (by positivity : 0 ≤ (B : ℝ)/ε₀)
    rw [div_mul_cancel₀ _ hε₀.ne'] at hb
    exact (hcoeff i hi hiD).trans
      (hb.trans (mul_le_mul_of_nonneg_right hCbig hε.le))
  · have hsmallε : ε < ε₀ := lt_of_not_ge hlargeε
    let Lreal := δ/(10*ε)
    let L := ⌊Lreal⌋₊
    have hX : 2*((W : ℝ)+1) ≤ Lreal := by
      apply (le_div_iff₀ (by positivity : 0 < 10*ε)).mpr
      have hh := (lt_div_iff₀ (by positivity : 0 < 20*((W : ℝ)+1))).mp hsmallε
      nlinarith only [hh]
    have hfloor := Nat.lt_floor_add_one Lreal
    have hWLr : (W : ℝ) ≤ L := by dsimp only [L]; linarith [Nat.cast_nonneg (α := ℝ) W]
    have hWL : W ≤ L := by exact_mod_cast hWLr
    have hL : 0 < L := hW.trans_le hWL
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hLlow : δ/(20*ε) ≤ (L : ℝ) := by
      have he : δ/(20*ε) = Lreal/2 := by dsimp only [Lreal]; ring
      rw [he]
      dsimp only [L]
      linarith [Nat.cast_nonneg (α := ℝ) W]
    have hLε : (L : ℝ)*ε ≤ δ/10 := by
      have hu : 0 ≤ Lreal := by dsimp only [Lreal]; positivity
      have hf := Nat.floor_le hu
      have hm := mul_le_mul_of_nonneg_right hf hε.le
      have he : Lreal*ε = δ/10 := by dsimp only [Lreal]; field_simp
      rw [he] at hm
      exact hm
    let R := fun q m : ℕ => ∀ i : ℕ, 0 < i → i ≤ D →
      ‖(((m : ℝ)*((q : ℝ)*p.coeff i) : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)/(N : ℝ)^i
    have hall : ∀ m ∈ Finset.range L, ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ R q m := by
      intro m hm
      have hmL : (m : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hm).le
      have hmε : (m : ℝ)*ε ≤ δ/10 :=
        (mul_le_mul_of_nonneg_right hmL hε.le).trans hLε
      have hscaled := scalar_polynomial_natural_multiple_small_value_density p N m δ ε (δ/10) hmε hdense
      obtain ⟨q, hq, hqB, hc⟩ := hcoarse (Polynomial.C (m : ℝ)*p)
        (scalar_polynomial_natural_multiple_degree p m D hp) N hN (δ/10) le_rfl hscaled
      refine ⟨q, hq, hqB, ?_⟩
      intro i hi hiD
      have hb := hc i hi hiD
      rw [coeff_C_mul] at hb
      have he : (m : ℝ)*((q : ℝ)*p.coeff i) = (q : ℝ)*((m : ℝ)*p.coeff i) := by ring
      rw [he]
      apply (le_div_iff₀ (pow_pos hNr i)).mpr
      nlinarith only [hb]
    obtain ⟨q, hq, hqB, hcommon⟩ := finite_bounded_candidate_density (Finset.range L) B hB R hall
    have hd : μ*(L : ℝ) ≤ ((Finset.range L).filter (R q)).card := by
      simp only [Finset.card_range] at hcommon
      have he : μ*(L : ℝ) = (L : ℝ)/(B : ℝ) := by dsimp only [μ]; ring
      rwa [he]
    have hLL : 8*(K : ℝ) ≤ μ*(L : ℝ) := by
      have hh := (div_le_iff₀ hμ).mp (hWbound.trans hWLr)
      nlinarith
    have hεcoeff : ∀ i : ℕ, 0 < i → (B : ℝ)/(N : ℝ)^i ≤ μ/10 := by
      intro i hi
      apply (div_le_iff₀ (pow_pos hNr i)).mpr
      have hTNreal : (T : ℝ) ≤ N := by exact_mod_cast hTN
      have hh := (div_le_iff₀ hμ).mp (hTbound.trans hTNreal)
      have hpow := mul_le_mul_of_nonneg_left (le_self_pow₀ hN1 hi.ne') hμ.le
      nlinarith
    have hcoordinates : ∀ i : Fin D, ∃ r : ℕ, 0 < r ∧ r ≤ K ∧
        (N : ℝ)^(i.val+1)*‖(((r : ℝ)*((q : ℝ)*p.coeff (i.val+1)) : ℝ) : UnitAddCircle)‖ ≤ Csmall*ε := by
      intro i
      have hsub : (Finset.range L).filter (R q) ⊆ (Finset.range L).filter (fun m : ℕ =>
          ‖((0+(m : ℝ)*((q : ℝ)*p.coeff (i.val+1)) : ℝ) : UnitAddCircle)‖ ≤
            (B : ℝ)/(N : ℝ)^(i.val+1)) := by
        intro m hm
        have hv := Finset.mem_filter.mp hm
        refine Finset.mem_filter.mpr ⟨hv.1, ?_⟩
        simpa only [zero_add] using hv.2 (i.val+1) (by omega) (by omega)
      have hdi : μ*(L : ℝ) ≤ ((Finset.range L).filter (fun m : ℕ =>
          ‖((0+(m : ℝ)*((q : ℝ)*p.coeff (i.val+1)) : ℝ) : UnitAddCircle)‖ ≤
            (B : ℝ)/(N : ℝ)^(i.val+1))).card :=
        hd.trans (by exact_mod_cast Finset.card_le_card hsub)
      obtain ⟨r, hr, hrK, hb⟩ := hrec ((q : ℝ)*p.coeff (i.val+1)) 0 L hL
        ((B : ℝ)/(N : ℝ)^(i.val+1)) (by positivity) (hεcoeff _ (by omega)) hLL hdi
      refine ⟨r, hr, hrK, ?_⟩
      exact polynomial_small_value_recurrence_rescale δ μ ε (L : ℝ) ((N : ℝ)^(i.val+1))
        ‖(((r : ℝ)*((q : ℝ)*p.coeff (i.val+1)) : ℝ) : UnitAddCircle)‖ (K : ℝ) (B : ℝ)
        hδ hμ hε (pow_pos hNr _) (norm_nonneg _) hLlow hb
    choose r hr hrK hrerr using hcoordinates
    obtain ⟨M, hM, hMK, hproduct⟩ := finite_mod_one_common_multiplier r K (by omega) hr hrK
    have hMK' : M ≤ K^(D+1) := by simpa using hMK
    let Q := M*q
    refine ⟨Q, Nat.mul_pos hM hq,
      (Nat.mul_le_mul hMK' hqB).trans (by dsimp only [S]; omega), ?_⟩
    intro j hj hjD
    let i : Fin D := ⟨j-1, by omega⟩
    have hij : i.val+1=j := by dsimp only [i]; omega
    have hb := hrerr i
    rw [hij] at hb
    let E := Csmall*ε/(N : ℝ)^j
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hnorm : ‖(((r i : ℝ)*((q : ℝ)*p.coeff j) : ℝ) : UnitAddCircle)‖ ≤ E := by
      apply (le_div_iff₀ (pow_pos hNr j)).mpr
      nlinarith only [hb]
    have hnormK : ‖(((r i : ℝ)*((q : ℝ)*p.coeff j) : ℝ) : UnitAddCircle)‖ ≤ (K : ℝ)*E := by
      have he := mul_le_mul_of_nonneg_right hK1 hE
      simp only [one_mul] at he
      exact hnorm.trans he
    have hprod := hproduct i ((q : ℝ)*p.coeff j) E hE hnormK
    simp only [Fintype.card_fin, Nat.cast_pow] at hprod
    have hscaled := mul_le_mul_of_nonneg_left hprod (pow_nonneg hNr.le j)
    have he : (N : ℝ)^j*((K : ℝ)^(D+1)*E) = (K : ℝ)^(D+1)*Csmall*ε := by
      dsimp only [E]
      field_simp
    rw [he] at hscaled
    have heQ : (Q : ℝ)*p.coeff j = (M : ℝ)*((q : ℝ)*p.coeff j) := by
      dsimp only [Q]
      push_cast
      ring
    rw [heQ]
    exact hscaled.trans (mul_le_mul_of_nonneg_right hCsm hε.le)

end Hindman168

