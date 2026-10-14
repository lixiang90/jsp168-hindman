import Hindman168.MaskGeneratedNormalizedIntegerRows
import Hindman168.AdditiveRowResidueIndependence
import Hindman168.NormalizedResponseResidueArithmetic

/-! Normalized base rows preserve nonzero polynomial minors modulo rough
primes. The proof uses integer cross multiplication and unit column scales;
it requires no numerical good tuple or translation denominator condition. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open scoped BigOperators Classical

theorem rows_pair_independent_of_nonzero_minor {R I : Type*} [CommRing R] [IsDomain R]
    (c e : I → R) (j k : I) (hminor : c j * e k - c k * e j ≠ 0) :
    LinearIndependent R ![c, e] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have hj : s * c j + t * e j = 0 := congrFun h j
  have hk : s * c k + t * e k = 0 := congrFun h k
  have hs : s * (c j * e k - c k * e j) = 0 := by
    calc
      _ = (s * c j + t * e j) * e k - (s * c k + t * e k) * e j := by ring
      _ = 0 := by rw [hj, hk]; ring
  have ht : t * (c j * e k - c k * e j) = 0 := by
    calc
      _ = (s * c k + t * e k) * c j - (s * c j + t * e j) * c k := by ring
      _ = 0 := by rw [hj, hk]; ring
  exact ⟨(mul_eq_zero.mp hs).resolve_right hminor, (mul_eq_zero.mp ht).resolve_right hminor⟩

namespace PolynomialRowFamily

variable {n r m : ℕ} {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
  {x : Fin n → ℕ} {c : Fin (m + 1) → ℕ} {W : ℕ}

theorem NormalizedIntegerRowConditions.coefficient_cross_multiply
    (H : F.NormalizedIntegerRowConditions x c W) (hc : ∀ k, 0 < c k)
    (i : Fin r) (k : Fin (m + 1)) :
    (c (F.normalizationAnchor i) : ℤ) * F.normalizedIntegerRow x c i k =
      (c k : ℤ) * MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k) := by
  have hne : (c (F.normalizationAnchor i) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
  have he : (c (F.normalizationAnchor i) : ℚ) * (F.normalizedIntegerRow x c i k : ℚ) =
      (c k : ℚ) * (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k) : ℚ) := by
    rw [H.coefficient_cast]
    field_simp
  exact_mod_cast he

theorem NormalizedIntegerRowConditions.minor_cross_multiply
    (H : F.NormalizedIntegerRowConditions x c W) (hc : ∀ k, 0 < c k)
    (i l : Fin r) (j k : Fin (m + 1)) :
    ((c (F.normalizationAnchor i) : ℤ) * c (F.normalizationAnchor l)) *
      (F.normalizedIntegerRow x c i j * F.normalizedIntegerRow x c l k -
        F.normalizedIntegerRow x c i k * F.normalizedIntegerRow x c l j) =
      ((c j : ℤ) * c k) * MvPolynomial.eval (fun v => (x v : ℤ))
        (polynomialRowMinor (F.row i) (F.row l) j k) := by
  calc
    _ = ((c (F.normalizationAnchor i) : ℤ) * F.normalizedIntegerRow x c i j) *
          ((c (F.normalizationAnchor l) : ℤ) * F.normalizedIntegerRow x c l k) -
        ((c (F.normalizationAnchor i) : ℤ) * F.normalizedIntegerRow x c i k) *
          ((c (F.normalizationAnchor l) : ℤ) * F.normalizedIntegerRow x c l j) := by ring
    _ = _ := by
      simp only [H.coefficient_cross_multiply hc, polynomialRowMinor, map_sub, map_mul]
      ring

theorem NormalizedIntegerRowConditions.residue_pair_independent
    (H : F.NormalizedIntegerRowConditions x c W) (hc : ∀ k, 0 < c k)
    (target i l : Fin r) (hil : i ≠ l) (p : ℕ) (hp : p.Prime)
    (hu : ∀ k, IsUnit (c k : ZMod p))
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) :
    LinearIndependent (ZMod p)
      ![(fun k => (F.normalizedIntegerRow x c i k : ZMod p)),
        (fun k => (F.normalizedIntegerRow x c l k : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, k, hminor⟩ := F.pair_minor i l hil.symm
  apply rows_pair_independent_of_nonzero_minor _ _ j k
  intro hz
  have he := congrArg (fun z : ℤ => (z : ZMod p)) (H.minor_cross_multiply hc i l j k)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast] at he
  rw [hz, mul_zero, integerPolynomialEval_residue] at he
  exact (mul_ne_zero (mul_ne_zero (hu j).ne_zero (hu k).ne_zero)
    (havoid _ (F.minor_mem_catalog target i l j k hminor))) he.symm

end PolynomialRowFamily
end Hindman168
