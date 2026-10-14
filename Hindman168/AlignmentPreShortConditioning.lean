import Hindman168.FiniteConditionedTailPivot
import Hindman168.AlignmentShortExposureLaw

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

def alignmentTailPivotIndex {n : ℕ} (i : Fin n) (T : Finset (Fin n)) : Option T → Fin n
  | none => i
  | some j => j.val

theorem alignmentTailPivotIndex_injective {n : ℕ} (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) : Function.Injective (alignmentTailPivotIndex i T) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim ((ne_of_lt (hT b.val b.property)) h.symm)
  | some a =>
    cases b with
    | none => exact False.elim ((ne_of_lt (hT a.val a.property)) h)
    | some b => exact congrArg some (Subtype.ext h)

noncomputable def alignmentPreShortEvent {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) (j : Fin n) (p : ℕ) : Prop :=
  if j ∈ T then p ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)
  else if j < i then p = x j else True

theorem alignmentPreShortEvent_all {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x y : Fin n → ℕ) :
    (∀ j, alignmentPreShortEvent F w i T x j (y j)) ↔
      (∀ j, j < i → j ∉ T → x j = y j) ∧
      (∀ j ∈ T, y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) := by
  constructor
  · intro h
    constructor
    · intro j hj ht
      have hh : y j = x j := by simpa only [alignmentPreShortEvent, if_neg ht, if_pos hj] using h j
      exact hh.symm
    · intro j hj
      simpa only [alignmentPreShortEvent, if_pos hj] using h j
  · rintro ⟨hout, htail⟩ j
    by_cases ht : j ∈ T
    · simpa only [alignmentPreShortEvent, if_pos ht] using htail j ht
    · by_cases hj : j < i
      · simpa only [alignmentPreShortEvent, if_neg ht, if_pos hj] using (hout j hj ht).symm
      · simp only [alignmentPreShortEvent, if_neg ht, if_neg hj]

theorem alignmentPreShortEvent_pivot {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hT : ∀ j ∈ T, j < i) : alignmentPreShortEvent F w i T x i = (fun _ => True) := by
  have hi : i ∉ T := fun h => (lt_irrefl i) (hT i h)
  funext p
  simp only [alignmentPreShortEvent, if_neg hi, lt_self_iff_false, if_false]

theorem alignmentPreShortEvent_tail {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) (j : T) :
    alignmentPreShortEvent F w i T x j.val =
      (fun p => p ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)) := by
  funext p
  simp only [alignmentPreShortEvent, if_pos j.property]

theorem alignmentPreShortEvent_pos
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (x : Fin n → ℕ) (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hZ : ∀ j : Fin n, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w)) (j : Fin n) :
    0 < event (rawMass (F.cutoff w j.val) (primorial w)) (alignmentPreShortEvent F w i T x j) := by
  have hn := Finsupp.mem_support_iff.mp hx
  rw [globalRawMass, piMass_apply] at hn
  have hj := Finsupp.mem_support_iff.mpr
    (Finset.prod_ne_zero_iff.mp hn j (Finset.mem_univ j))
  apply event_pos_of_supported_witness _ _
    (fun p => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hZ j) p)
    hj
  unfold alignmentPreShortEvent
  split_ifs
  · exact binaryDyadicResidueWindow_anchor (alignmentGlobalRawMass_support_positive hF w x hx j)
  · rfl

end Hindman168
