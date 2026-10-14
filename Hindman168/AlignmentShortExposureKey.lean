import Hindman168.AlignmentRawExposure
import Hindman168.MasterMicrocellGrowth

/-! The literal short-bin exposure: earlier outside values, inside residues
and dyadic bins, pivot residue, and product short bin. No pivot cell is frozen. -/

namespace Hindman168

open scoped BigOperators Classical

def alignmentShortExposureKey {n : ℕ} (F : MasterParameterFamily) (w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (x : Fin n → ℕ) :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) × ℕ × ℕ :=
  ((fun j => if j < i ∧ j ∉ T then x j else 0),
   (fun j => if j ∈ T then x j % ((F.modulus w : ℕ) * (primorial w) ^ w) else 0),
   (fun j => if j ∈ T then Nat.log2 (x j) else 0),
   x i % (F.modulus w : ℕ),
   (alignmentNaturalBlockProduct x T * x i) /
     ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)))

theorem alignmentShortExposureKey_rawExposure {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T x y := by
  constructor
  · intro j hj hjT
    have hh := congrArg (fun z => z.1 j) h
    simpa only [alignmentShortExposureKey, if_pos (And.intro hj hjT)] using hh
  · intro j hj
    have hh := congrArg (fun z => z.2.1 j) h
    change x j % ((F.modulus w : ℕ) * (primorial w) ^ w) =
      y j % ((F.modulus w : ℕ) * (primorial w) ^ w)
    simpa only [alignmentShortExposureKey, if_pos hj] using hh

theorem alignmentShortExposureKey_dyadic_eq {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    ∀ j ∈ T, Nat.log2 (x j) = Nat.log2 (y j) := by
  intro j hj
  have hh := congrArg (fun z => z.2.2.1 j) h
  simpa only [alignmentShortExposureKey, if_pos hj] using hh

theorem alignmentShortExposureKey_pivot_residue {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    Nat.ModEq (F.modulus w : ℕ) (x i) (y i) := by
  change x i % (F.modulus w : ℕ) = y i % (F.modulus w : ℕ)
  exact congrArg (fun z => z.2.2.2.1) h

theorem alignmentShortExposureKey_lower_product {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    (∏ j ∈ T, 2 ^ Nat.log2 (x j)) = ∏ j ∈ T, 2 ^ Nat.log2 (y j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [alignmentShortExposureKey_dyadic_eq F w i T h j hj]

theorem alignmentShortExposureKey_product_bin {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    (alignmentNaturalBlockProduct x T * x i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) =
      (alignmentNaturalBlockProduct y T * y i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) := by
  have hh := congrArg (fun z => z.2.2.2.2) h
  change _ / _ = _ / _ at hh
  rw [alignmentShortExposureKey_lower_product F w i T h] at hh ⊢
  exact hh

theorem alignmentShortExposureKey_dyadic_window {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (j : Fin n) (hj : j ∈ T) (hy : 0 < y j) :
    2 ^ Nat.log2 (x j) ≤ y j ∧ y j < 2 * 2 ^ Nat.log2 (x j) := by
  rw [alignmentShortExposureKey_dyadic_eq F w i T h j hj]
  exact ⟨Nat.log2_self_le hy.ne', by simpa only [pow_succ, mul_comm] using
    (Nat.lt_log2_self (n := y j))⟩

end Hindman168
