import Hindman168.MaskGeneratedIntegerTranslations

/-!
# Fixed polynomial size bounds for the actual integer directions

The signed cofactor construction has numerator bounds without assuming
integrality as an extra hypothesis. The finite formal coordinates and
denominator yield one exponent, independent of w, x, c and all functions.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem normalizedIntegerCoordinate_natAbs_le (M c cstar w : ℕ) (D d b : ℤ) :
    (normalizedIntegerCoordinate M c cstar w D d b).natAbs ≤
      M * cstar * b.natAbs * D.natAbs := by
  have hs : D.sign.natAbs ≤ 1 := by rw [Int.natAbs_sign]; split_ifs <;> omega
  unfold normalizedIntegerCoordinate
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ 1 * M * cstar * b.natAbs * D.natAbs :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.mul_le_mul hs (Nat.div_le_self _ _)))) (Int.natAbs_ediv_le_natAbs D d)
    _ = _ := by simp

theorem normalizedRootIntegerCoordinate_natAbs_le (M c cstar : ℕ) (b : ℤ) :
    (normalizedRootIntegerCoordinate M c cstar b).natAbs ≤ M * cstar * b.natAbs := by
  unfold normalizedRootIntegerCoordinate
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_self _ _))

theorem integerPolynomial_eval_fixed_power_cap {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) {B : ℕ}
    (hB : 2 ≤ B) (hx : ∀ k, x k ≤ B) :
    (MvPolynomial.eval (fun k => (x k : ℤ)) f).natAbs ≤
      B ^ (integerPolynomialCoeffSize f + f.totalDegree) := by
  have he := integerPolynomial_eval_natAbs_le f (fun k => (x k : ℤ)) (B := B)
    (by omega) (fun k => by simpa only [Int.natAbs_natCast] using hx k)
  have hC : integerPolynomialCoeffSize f ≤ B ^ integerPolynomialCoeffSize f :=
    (show integerPolynomialCoeffSize f < 2 ^ integerPolynomialCoeffSize f from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hB _)
  exact he.trans (by simpa only [pow_add] using Nat.mul_le_mul_right (B ^ f.totalDegree) hC)

namespace PolynomialRowFamily

variable {n r m : ℕ}

noncomputable def translationSizeExponent
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target : Fin r) : ℕ :=
  2 + (integerPolynomialCoeffSize (F.denominator target) + (F.denominator target).totalDegree) +
    Finset.univ.sup (fun p : Fin r × Fin (m + 1) =>
      integerPolynomialCoeffSize (F.direction p.1 p.2) + (F.direction p.1 p.2).totalDegree)

theorem translationSizeExponent_coordinate_le
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target i : Fin r)
    (k : Fin (m + 1)) :
    2 + (integerPolynomialCoeffSize (F.direction i k) + (F.direction i k).totalDegree) +
      (integerPolynomialCoeffSize (F.denominator target) + (F.denominator target).totalDegree) ≤
      F.translationSizeExponent target := by
  have h := Finset.le_sup (f := fun p : Fin r × Fin (m + 1) =>
    integerPolynomialCoeffSize (F.direction p.1 p.2) + (F.direction p.1 p.2).totalDegree)
    (Finset.mem_univ (i, k))
  dsimp only at h
  dsimp [translationSizeExponent]
  omega

theorem integerTranslation_size_bound
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r) (k : Fin (m + 1)) {B : ℕ}
    (hB : 2 ≤ B) (hM : (master.modulus w : ℕ) ≤ B)
    (hc : ∀ j, c j ≤ (master.modulus w : ℕ)) (hx : ∀ j, x j ≤ B) :
    (F.integerTranslation master w c x target i k).natAbs ≤
      B ^ F.translationSizeExponent target := by
  have hdir := integerPolynomial_eval_fixed_power_cap (F.direction i k) x hB hx
  have hden := integerPolynomial_eval_fixed_power_cap (F.denominator target) x hB hx
  have hcoord := normalizedIntegerCoordinate_natAbs_le (master.modulus w) (c k)
    (c (F.normalizationAnchor target)) w
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k))
  calc
    _ ≤ _ := hcoord
    _ ≤ B * B * B ^ (integerPolynomialCoeffSize (F.direction i k) + (F.direction i k).totalDegree) *
        B ^ (integerPolynomialCoeffSize (F.denominator target) + (F.denominator target).totalDegree) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hM ((hc _).trans hM)) hdir) hden
    _ = B ^ (2 + (integerPolynomialCoeffSize (F.direction i k) + (F.direction i k).totalDegree) +
        (integerPolynomialCoeffSize (F.denominator target) + (F.denominator target).totalDegree)) := by
      simp only [pow_add, pow_two]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (F.translationSizeExponent_coordinate_le target i k)

theorem rootIntegerTranslation_size_bound
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (k : Fin (m + 1)) {B : ℕ}
    (hB : 2 ≤ B) (hM : (master.modulus w : ℕ) ≤ B)
    (hc : ∀ j, c j ≤ (master.modulus w : ℕ)) (hx : ∀ j, x j ≤ B) :
    (F.rootIntegerTranslation master w c x target k).natAbs ≤
      B ^ F.translationSizeExponent target := by
  have hdir := integerPolynomial_eval_fixed_power_cap (F.direction target k) x hB hx
  have hcoord := normalizedRootIntegerCoordinate_natAbs_le (master.modulus w) (c k)
    (c (F.normalizationAnchor target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction target k))
  calc
    _ ≤ _ := hcoord
    _ ≤ B * B * B ^ (integerPolynomialCoeffSize (F.direction target k) +
        (F.direction target k).totalDegree) :=
      Nat.mul_le_mul (Nat.mul_le_mul hM ((hc _).trans hM)) hdir
    _ = B ^ (2 + (integerPolynomialCoeffSize (F.direction target k) +
        (F.direction target k).totalDegree)) := by simp only [pow_add, pow_two]
    _ ≤ _ := Nat.pow_le_pow_right (by omega)
      ((Nat.le_add_right _ _).trans (F.translationSizeExponent_coordinate_le target target k))

end PolynomialRowFamily

open Filter
open FiniteMass
open scoped Topology

theorem maskGenerated_integer_translation_size_bounds (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (block : ℕ → Fin (m + 1) → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support, ∀ i k,
      (((maskGeneratedRowDataFamily m gap t).rows.integerTranslation (maskGeneratedMaster m gap)
        w (masterColumnCoefficient N a block w) x (maskGeneratedRowDataFamily m gap t).target i k).natAbs ≤
        (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
          (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^
            (maskGeneratedRowDataFamily m gap t).rows.translationSizeExponent
              (maskGeneratedRowDataFamily m gap t).target) ∧
      (((maskGeneratedRowDataFamily m gap t).rows.rootIntegerTranslation (maskGeneratedMaster m gap)
        w (masterColumnCoefficient N a block w) x (maskGeneratedRowDataFamily m gap t).target k).natAbs ≤
        (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
          (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^
            (maskGeneratedRowDataFamily m gap t).rows.translationSizeExponent
              (maskGeneratedRowDataFamily m gap t).target) := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hb := hF.column_coefficients_bounds a
    (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) block hblock hnonempty
  filter_upwards [hb] with w hw
  intro t x hx i k
  let B := ((maskGeneratedMaster m gap).pool w (gap w).val).upper +
    (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hB : 2 ≤ B := by
    have h := (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
    dsimp [B]
    omega
  have hM : ((maskGeneratedMaster m gap).modulus w : ℕ) ≤ B := by
    have h := (maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val
    dsimp [B]
    omega
  have hxp : ∀ j, x j ≤ B := by
    intro j
    have h := (primePool_mem.mp (primeIndependentMass_support_pool hx j)).2.1
    dsimp [B]
    omega
  exact ⟨(maskGeneratedRowDataFamily m gap t).rows.integerTranslation_size_bound
      (maskGeneratedMaster m gap) w (masterColumnCoefficient N a block w) x _ i k hB hM
      (fun j => (hw j).2.2) hxp,
    (maskGeneratedRowDataFamily m gap t).rows.rootIntegerTranslation_size_bound
      (maskGeneratedMaster m gap) w (masterColumnCoefficient N a block w) x _ k hB hM
      (fun j => (hw j).2.2) hxp⟩

end Hindman168
