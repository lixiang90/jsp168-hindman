import Hindman168.DyadicCoprimalityRecurrence

/-!
# Uniform certificates for actual dyadic rough-coprimality bounds

The cutoff, dyadic threshold and error coefficient are fixed before the
endpoint arrays are chosen. Main-coordinate certificates temporarily
require both coordinate-zero endpoints to be maximal; a finite family of
such certificates can be made uniform over all variable permutations.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def dyadicCoprimeError (w L : ℕ) : ℝ :=
  1 / (w : ℝ) + Real.log (L : ℝ) / Real.sqrt L

def DyadicCoprimeControl {m n : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (w0 e0 K : ℕ) : Prop :=
  ∀ (eF : Fin m → ℕ) (eG : Fin n → ℕ),
    (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) → ∀ w L : ℕ,
    w0 ≤ w → 0 < w → Real.exp 2 ≤ (L : ℝ) →
    (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
    dyadicCommonPrimeMass eF eG w F G ≤ (K : ℝ) * dyadicCoprimeError w L

def DyadicMainCoprimeControl {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (w0 e0 K : ℕ) : Prop :=
  ∀ (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ),
    (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) →
    (∀ i, eF i ≤ eF 0) → (∀ i, eG i ≤ eG 0) → ∀ w L : ℕ,
    w0 ≤ w → 0 < w → Real.exp 2 ≤ (L : ℝ) →
    (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
    dyadicCommonPrimeMass eF eG w F G ≤ (K : ℝ) * dyadicCoprimeError w L

theorem dyadicCoprimeError_nonneg {w L : ℕ} (hL : Real.exp 2 ≤ (L : ℝ)) :
    0 ≤ dyadicCoprimeError w L := by
  have hLone : 1 ≤ (L : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).le.trans hL
  exact add_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg w))
    (div_nonneg (Real.log_nonneg hLone) (Real.sqrt_nonneg _))

theorem dyadicCoprimeControl_mono {m n w0 e0 K w1 e1 K1 : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (h : DyadicCoprimeControl F G w0 e0 K)
    (hw : w0 ≤ w1) (he : e0 ≤ e1) (hK : K ≤ K1) :
    DyadicCoprimeControl F G w1 e1 K1 := by
  intro eF eG heF heG w L hww hwpos hL hLF hLG
  exact (h eF eG (fun i => he.trans (heF i)) (fun i => he.trans (heG i))
    w L (hw.trans hww) hwpos hL hLF hLG).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (dyadicCoprimeError_nonneg hL))

theorem dyadicMainCoprimeControl_mono {m n w0 e0 K w1 e1 K1 : ℕ}
    {F : MvPolynomial (Fin (m + 1)) ℤ} {G : MvPolynomial (Fin (n + 1)) ℤ}
    (h : DyadicMainCoprimeControl F G w0 e0 K)
    (hw : w0 ≤ w1) (he : e0 ≤ e1) (hK : K ≤ K1) :
    DyadicMainCoprimeControl F G w1 e1 K1 := by
  intro eF eG heF heG hmaxF hmaxG w L hww hwpos hL hLF hLG
  exact (h eF eG (fun i => he.trans (heF i)) (fun i => he.trans (heG i))
    hmaxF hmaxG w L (hw.trans hww) hwpos hL hLF hLG).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (dyadicCoprimeError_nonneg hL))

theorem dyadicCommonPrimeMass_swap {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    dyadicCommonPrimeMass eG eF w G F = dyadicCommonPrimeMass eF eG w F G :=
  dyadic_commonPrimeEvent_swap eF eG F G

theorem dyadicCommonPrimeMass_reindex {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    dyadicCommonPrimeMass (fun i => eF (s i)) (fun i => eG (t i)) w
      (MvPolynomial.rename s.symm F) (MvPolynomial.rename t.symm G) =
      dyadicCommonPrimeMass eF eG w F G :=
  dyadic_commonPrimeEvent_reindex eF eG s t F G

theorem dyadicCoprimeControl_swap {m n w0 e0 K : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (h : DyadicCoprimeControl F G w0 e0 K) :
    DyadicCoprimeControl G F w0 e0 K := by
  intro eG eF heG heF w L hww hwpos hL hLG hLF
  rw [dyadicCommonPrimeMass_swap]
  exact h eF eG heF heG w L hww hwpos hL hLF hLG

theorem dyadicCoprimeControl_empty_left {n : ℕ}
    (F : MvPolynomial (Fin 0) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    DyadicCoprimeControl F G (F.coeff 0).natAbs 0 0 := by
  intro eF eG _ _ w L hw _ _ _ _
  unfold dyadicCommonPrimeMass
  rw [F.eq_C_of_isEmpty, commonPrimeEvent_constant_event_zero _ hw]
  simp

theorem finite_uniform_dyadic_main_controls {ι : Type*} [Fintype ι] {m n : ℕ}
    (F : ι → MvPolynomial (Fin (m + 1)) ℤ)
    (G : ι → MvPolynomial (Fin (n + 1)) ℤ)
    (h : ∀ i, ∃ w0 e0 K : ℕ, DyadicMainCoprimeControl (F i) (G i) w0 e0 K) :
    ∃ w0 e0 K : ℕ, ∀ i, DyadicMainCoprimeControl (F i) (G i) w0 e0 K := by
  classical
  choose w e K hk using h
  refine ⟨Finset.univ.sup w, Finset.univ.sup e, Finset.univ.sup K, ?_⟩
  intro i
  exact dyadicMainCoprimeControl_mono (hk i)
    (Finset.le_sup (Finset.mem_univ i)) (Finset.le_sup (Finset.mem_univ i))
    (Finset.le_sup (Finset.mem_univ i))

end Hindman168
