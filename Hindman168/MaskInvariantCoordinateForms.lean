import Hindman168.MaskRemovalTailScalarWeights
import Hindman168.PolynomialNormalizedIntegerRows

/-! Scalar identities for the actual integer-normalized invariant rows.
The balanced substitution is cleared by p, so exact division is used only
with the stated coordinate divisibility. No rational row values are used. -/

namespace Hindman168

open scoped BigOperators Classical

variable {n r m : ℕ}

def maskSingleTag (u : Fin (m + 1)) (j : Fin (m + 1)) : Fin 3 :=
  if j = u then 1 else 0

def maskBalancedTag (u v : Fin (m + 1)) (j : Fin (m + 1)) : Fin 3 :=
  if j = u then 1 else if j = v then 2 else 0

def maskSingleScalar (p : ℕ) (t : Fin 3) : ℕ := if t = 1 then p else 1

def maskBalancedClearScalar (p : ℕ) (t : Fin 3) : ℕ :=
  if t = 1 then 1 else if t = 2 then p ^ 2 else p

def maskAbsorbedScalar (p q : ℕ) (t : Fin 3) : ℕ :=
  if t = 1 then q else if t = 2 then p else 1

theorem PolynomialRowFamily.normalizedIntegerRow_eq_zero_of_symbolic
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (j : Fin (m + 1))
    (hj : F.row i j = 0) : F.normalizedIntegerRow x c i j = 0 := by
  simp [PolynomialRowFamily.normalizedIntegerRow, hj]

theorem PolynomialRowFamily.normalizedIntegerLinearForm_tag_scaled
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (tag : Fin (m + 1) → Fin 3) (hi : maskRowInvariant (F.row i) tag)
    (α : Fin 3 → ℕ) (z : Fin (m + 1) → ℤ) :
    F.normalizedIntegerLinearForm x c i (fun j => (α (tag j) : ℤ) * z j) =
      (α (tag (F.normalizationAnchor i)) : ℤ) * F.normalizedIntegerLinearForm x c i z := by
  unfold PolynomialRowFamily.normalizedIntegerLinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  by_cases hj : F.row i j = 0
  · rw [F.normalizedIntegerRow_eq_zero_of_symbolic x c i j hj]
    ring
  · rw [hi j (F.normalizationAnchor i) hj (F.normalizationAnchor_ne_zero i)]
    ring

theorem PolynomialRowFamily.normalizedIntegerLinearForm_const_scaled
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (b : ℤ)
    (z : Fin (m + 1) → ℤ) :
    F.normalizedIntegerLinearForm x c i (fun j => b * z j) =
      b * F.normalizedIntegerLinearForm x c i z := by
  unfold PolynomialRowFamily.normalizedIntegerLinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem maskSingleCoordinates_tag_scaled (u : Fin (m + 1)) (p : ℕ)
    (z : Fin (m + 1) → ℤ) :
    Function.update z u ((p : ℤ) * z u) =
      fun j => (maskSingleScalar p (maskSingleTag u j) : ℤ) * z j := by
  funext j
  by_cases hj : j = u <;> simp [maskSingleScalar, maskSingleTag, hj]

theorem maskBalancedCoordinates_cleared_tag (u v : Fin (m + 1)) (hne : u ≠ v)
    (p : ℕ) (z : Fin (m + 1) → ℤ) (hd : (p : ℤ) ∣ z u) :
    (fun j => (p : ℤ) * maskBalancedCoordinates u v p z j) =
      fun j => (maskBalancedClearScalar p (maskBalancedTag u v j) : ℤ) * z j := by
  funext j
  by_cases hj : j = u
  · subst j
    simpa [maskBalancedCoordinates, maskBalancedTag, maskBalancedClearScalar, hne, mul_comm]
      using Int.ediv_mul_cancel hd
  · by_cases hv : j = v
    · subst j
      simp [maskBalancedCoordinates, maskBalancedTag, maskBalancedClearScalar, Ne.symm hne,
        pow_two, mul_assoc]
    · simp [maskBalancedCoordinates, maskBalancedTag, maskBalancedClearScalar, hj, hv]

theorem maskAbsorbedCoordinates_tag_scaled (u v : Fin (m + 1)) (hne : u ≠ v)
    (p q : ℕ) (z : Fin (m + 1) → ℤ) :
    maskAbsorbedCoordinates u v p q z =
      fun j => (maskAbsorbedScalar p q (maskBalancedTag u v j) : ℤ) * z j := by
  funext j
  by_cases hj : j = u
  · subst j
    simp [maskAbsorbedCoordinates, maskBalancedTag, maskAbsorbedScalar, hne]
  · by_cases hv : j = v
    · subst j
      simp [maskAbsorbedCoordinates, maskBalancedTag, maskAbsorbedScalar, Ne.symm hne]
    · simp [maskAbsorbedCoordinates, maskBalancedTag, maskAbsorbedScalar, hj, hv]

theorem PolynomialRowFamily.invariantIntegerForm_single
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u : Fin (m + 1)) (hi : maskRowInvariant (F.row i) (maskSingleTag u))
    (p : ℕ) (z : Fin (m + 1) → ℤ) :
    F.normalizedIntegerLinearForm x c i (Function.update z u ((p : ℤ) * z u)) =
      (maskSingleScalar p (maskSingleTag u (F.normalizationAnchor i)) : ℤ) *
        F.normalizedIntegerLinearForm x c i z := by
  rw [maskSingleCoordinates_tag_scaled]
  exact F.normalizedIntegerLinearForm_tag_scaled x c i _ hi _ z

theorem PolynomialRowFamily.invariantIntegerForm_balanced_cleared
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u v : Fin (m + 1)) (hne : u ≠ v)
    (hi : maskRowInvariant (F.row i) (maskBalancedTag u v))
    (p : ℕ) (z : Fin (m + 1) → ℤ) (hd : (p : ℤ) ∣ z u) :
    (p : ℤ) * F.normalizedIntegerLinearForm x c i (maskBalancedCoordinates u v p z) =
      (maskBalancedClearScalar p (maskBalancedTag u v (F.normalizationAnchor i)) : ℤ) *
        F.normalizedIntegerLinearForm x c i z := by
  rw [← F.normalizedIntegerLinearForm_const_scaled, maskBalancedCoordinates_cleared_tag u v hne p z hd]
  exact F.normalizedIntegerLinearForm_tag_scaled x c i _ hi _ z

theorem PolynomialRowFamily.invariantIntegerForm_absorbed
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u v : Fin (m + 1)) (hne : u ≠ v)
    (hi : maskRowInvariant (F.row i) (maskBalancedTag u v))
    (p q : ℕ) (z : Fin (m + 1) → ℤ) :
    F.normalizedIntegerLinearForm x c i (maskAbsorbedCoordinates u v p q z) =
      (maskAbsorbedScalar p q (maskBalancedTag u v (F.normalizationAnchor i)) : ℤ) *
        F.normalizedIntegerLinearForm x c i z := by
  rw [maskAbsorbedCoordinates_tag_scaled u v hne]
  exact F.normalizedIntegerLinearForm_tag_scaled x c i _ hi _ z

end Hindman168
