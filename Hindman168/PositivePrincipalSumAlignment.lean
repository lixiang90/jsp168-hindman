import Hindman168.PositivePrincipalSumPointwise
import Hindman168.AlignmentAddingPairs
import Hindman168.PrincipalBlockCalibration

/-!
# Restricting the original adding-pair alignment event to a selected chain

Every earlier chain block is an eligible adding block for its later block.
The sum over those original adding pairs equals the normalized subset row
exactly. Thus the alignment implication in (2.12), rather than an assumed
lower bound for model counts, supplies all row thresholds.
-/

namespace Hindman168
open scoped BigOperators Classical

/-- The original adding-pair alignment condition for a fixed scale vector
and fixed color model. Integer coefficient ratios are the original ratios
at stages where the master integrality conditions hold. -/
def PrincipalAddingAlignment {n : ℕ} (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (b : Fin n → ℚ) (w : ℕ) (S : Finset (Fin n) → Fin n → ℤ → ℝ)
    (θ : ℝ) (x : Fin n → ℕ) : Prop :=
  ∀ (T : Finset (Fin n)) (i : Fin n), T.Nonempty → (∀ k ∈ T, k < i) →
    ∀ D : Finset (AlignmentAddingPair n i), (∀ p ∈ D, p.targetTail = T) →
    2 * θ < S T i (principalSubsetProduct (insert i T) x) →
    θ < S T i ((principalSubsetProduct (insert i T) x : ℤ) +
      ∑ p ∈ D,
        ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
            (∏ k ∈ alignmentPairSourceBlock p, b k) w /
          principalBlockCoefficient M e T i (∏ k ∈ insert i T, b k) w : ℕ) : ℤ) *
          principalSubsetProduct (alignmentPairSourceBlock p) x)

def principalChainAddingPair {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (k d : Fin m) (hkd : k < d) : AlignmentAddingPair n (C.pivot d) where
  sourceTail := C.tail k
  targetTail := C.tail d
  sourcePivot := C.pivot k
  source_nonempty := C.tail_nonempty k
  target_nonempty := C.tail_nonempty d
  source_before_target := C.tail_before k d hkd
  target_before_sourcePivot := C.tails_before_pivots d k
  sourcePivot_before := C.pivot_strictMono hkd

/-- The adding-pair statement (2.12) gives the exact normalized row
threshold for every nonempty subset of any selected principal chain. -/
theorem principal_adding_alignment_chain_rows {n m M : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (b : Fin n → ℚ) (w : ℕ) (S : Finset (Fin n) → Fin n → ℤ → ℝ)
    (θ : ℝ) (x : Fin n → ℕ)
    (hc : ∀ i, 0 < C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w i)
    (halign : PrincipalAddingAlignment M e b w S θ x)
    (U : NonemptyColumnSubset (m+1))
    (hcenter : 2 * θ < S (C.tail (U.val.max' U.property)) (C.pivot (U.val.max' U.property))
      (C.sampleProducts x (U.val.max' U.property))) :
    θ < S (C.tail (U.val.max' U.property)) (C.pivot (U.val.max' U.property))
      (maskSubsetIntegerForm (C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w) U
        (fun k => (C.sampleProducts x k : ℤ))) := by
  let d := U.val.max' U.property
  let K := U.val.erase d
  have hkd (k : K) : k.val < d := by
    have hk := Finset.mem_erase.mp k.property
    exact lt_of_le_of_ne (U.val.le_max' k.val hk.2) hk.1
  let pair (k : K) := principalChainAddingPair C k.val d (hkd k)
  let D : Finset (AlignmentAddingPair n (C.pivot d)) := K.attach.image pair
  have hinj : Function.Injective pair := by
    intro k l h
    apply Subtype.ext
    apply C.pivot_strictMono.injective
    exact congrArg AlignmentAddingPair.sourcePivot h
  have htarget : ∀ p ∈ D, p.targetTail = C.tail d := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    rfl
  have hh := halign (C.tail d) (C.pivot d) (C.tail_nonempty d)
    (C.tails_before_pivots d d) D htarget hcenter
  let c := C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w
  have hsum : (∑ p ∈ D,
      ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
          (∏ k ∈ alignmentPairSourceBlock p, b k) w /
        principalBlockCoefficient M e (C.tail d) (C.pivot d)
          (∏ k ∈ insert (C.pivot d) (C.tail d), b k) w : ℕ) : ℤ) *
        principalSubsetProduct (alignmentPairSourceBlock p) x) =
      ∑ k ∈ K, ((c k / c d : ℕ) : ℤ) * C.sampleProducts x k := by
    rw [Finset.sum_image hinj.injOn]
    exact Finset.sum_attach K (fun k => ((c k / c d : ℕ) : ℤ) * C.sampleProducts x k)
  have hrow : maskSubsetIntegerForm c U (fun k => (C.sampleProducts x k : ℤ)) =
      (C.sampleProducts x d : ℤ) + ∑ k ∈ K, ((c k / c d : ℕ) : ℤ) * C.sampleProducts x k := by
    unfold maskSubsetIntegerForm
    rw [← Finset.sum_erase_add U.val
      (fun k => ((c k / c d : ℕ) : ℤ) * C.sampleProducts x k) (U.val.max'_mem U.property)]
    have hcd : c d / c d = 1 := Nat.div_self (hc d)
    change (∑ k ∈ K, ((c k / c d : ℕ) : ℤ) * C.sampleProducts x k) +
      ((c d / c d : ℕ) : ℤ) * C.sampleProducts x d = _
    rw [hcd]
    simp only [Nat.cast_one, one_mul]
    exact add_comm _ _
  rw [hsum] at hh
  rw [hrow]
  exact hh

end Hindman168
