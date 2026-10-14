import Hindman168.MaskGeneratedPrimeArithmetic
import Hindman168.NormalizedTranslationArithmetic
import Mathlib.Data.Finset.Max

/-!
# Maximum-support anchors and actual evaluated row responses

The paper's normalization anchor is the last nonzero column; it is
separate from the anchor used to construct each polynomial direction.
Good tuple exclusion yields the actual smooth-part divisibility bound.
-/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def support (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) : Finset (Fin (m + 1)) := Finset.univ.filter (fun k => F.row i k ≠ 0)

theorem support_nonempty (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) : (F.support i).Nonempty :=
  ⟨F.anchor i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.anchor_ne_zero i⟩⟩

noncomputable def normalizationAnchor (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) : Fin (m + 1) := (F.support i).max' (F.support_nonempty i)

theorem normalizationAnchor_ne_zero (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) : F.row i (F.normalizationAnchor i) ≠ 0 :=
  (Finset.mem_filter.mp (Finset.max'_mem (F.support i) (F.support_nonempty i))).2

theorem le_normalizationAnchor (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) (k : Fin (m + 1)) (hk : F.row i k ≠ 0) :
    k ≤ F.normalizationAnchor i :=
  (F.support i).le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

theorem row_zero_above_normalizationAnchor
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (i : Fin r) (k : Fin (m + 1)) (hk : F.normalizationAnchor i < k) : F.row i k = 0 := by
  by_contra h
  exact (not_le_of_gt hk) (F.le_normalizationAnchor i k h)

theorem evaluated_direction_response (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (l i : Fin r) :
    (∑ k, MvPolynomial.eval (fun j => (x j : ℤ)) (F.row l k) *
      MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k)) =
      MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l i) := by
  simp [response, polynomialRowResponse]

theorem evaluated_denominator (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (target : Fin r) :
    MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target) =
      ∏ i ∈ Finset.univ.erase target, MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i) := by
  simp [denominator]

theorem evaluated_response_dvd_denominator
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (target i : Fin r) (hi : i ≠ target) :
    MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i) ∣
      MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target) := by
  rw [F.evaluated_denominator]
  exact Finset.dvd_prod_of_mem (fun j => MvPolynomial.eval (fun k => (x k : ℤ))
    (F.response target j)) (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)

theorem local_good_smooth_part_dvd (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (target : Fin r) (master : MasterParameterFamily) (w : ℕ) (x : Fin n → ℕ)
    (hx : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    smoothPartNat w (MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target)).natAbs ∣
      (primorial w) ^ (master.exponent w - 1) := by
  have hD := predictionLocalPrimeGoodEvent_den_nonzero master _ _ (F.denominator_mem_catalog target) w x hx
  apply smoothPartNat_dvd_primorial_pow (Int.natAbs_ne_zero.mpr hD)
  intro p hp hpw hd
  apply hx.2
  exact ⟨⟨p, hp⟩, (smallPrimeLabels_mem w ⟨p, hp⟩).mpr hpw, Int.natCast_dvd.mpr hd⟩

noncomputable def normalizedLinearForm (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (z : Fin (m + 1) → ℤ) : ℚ :=
  ∑ k, ((c k : ℚ) / c (F.normalizationAnchor i)) *
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k) : ℚ) * (z k : ℚ)

end Hindman168.PolynomialRowFamily
