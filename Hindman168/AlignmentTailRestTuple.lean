import Hindman168.AlignmentActualRetainedScaleRange
import Hindman168.AlignmentMasterRetainedCRT
import Hindman168.FinitePivotCoordinates

/-! Insert the ACTUAL independent tail coordinates into the original anchor.
Changing the removed factor is exactly one coordinate update. All retained
products and CRT representatives therefore stay fixed before it varies. -/
namespace Hindman168
open FiniteMass
open scoped Classical BigOperators

noncomputable def alignmentTailTuple {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (tail : T → ℕ) : Fin N → ℕ :=
  fun k => if hk : k ∈ T then tail ⟨k,hk⟩ else x k

theorem alignment_tail_tuple_inside {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (tail : T → ℕ) (k : T) :
    alignmentTailTuple T x tail k.val=tail k := by
  simp only [alignmentTailTuple,dif_pos k.property]

theorem alignment_tail_tuple_outside {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (tail : T → ℕ) (k : Fin N) (hk : k ∉ T) :
    alignmentTailTuple T x tail k=x k := by
  simp only [alignmentTailTuple,dif_neg hk]

theorem alignment_tail_rest_tuple_update {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (j : T) (rest : {k : T // k ≠ j} → ℕ) (z t : ℕ) :
    alignmentTailTuple T x (insertPivotCoordinate j rest t) =
      Function.update (alignmentTailTuple T x (insertPivotCoordinate j rest z)) j.val t := by
  funext k
  by_cases hkj : k=j.val
  · subst k
    rw [Function.update_self,alignment_tail_tuple_inside,insertPivotCoordinate_self]
  · rw [Function.update_of_ne hkj]
    by_cases hk : k ∈ T
    · simp only [alignmentTailTuple,dif_pos hk,insertPivotCoordinate]
      have hn : (⟨k,hk⟩ : T) ≠ j := by intro he; exact hkj (congrArg Subtype.val he)
      simp only [dif_neg hn]
    · simp only [alignmentTailTuple,dif_neg hk]

theorem alignment_tail_tuple_cast_update {N : ℕ} (y : Fin N → ℕ) (j : Fin N) (t : ℕ) :
    (fun k => (Function.update y j t k : ℝ)) = Function.update (fun k => (y k : ℝ)) j (t : ℝ) := by
  funext k
  by_cases hk : k=j
  · subst k; rw [Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hk,Function.update_of_ne hk]

theorem alignment_tail_rest_retained_product {N : ℕ} (T U : Finset (Fin N))
    (x : Fin N → ℕ) (j : T) (hj : j.val ∉ U)
    (rest : {k : T // k ≠ j} → ℕ) (z t : ℕ) :
    alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest t)) U =
      alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest z)) U := by
  rw [alignment_tail_rest_tuple_update T x j rest z t]
  exact alignment_retained_product_update _ U j.val hj t

theorem alignment_tail_rest_retained_representative {N : ℕ} (T U : Finset (Fin N))
    (x : Fin N → ℕ) (j : T) (hj : j.val ∉ U)
    (rest : {k : T // k ≠ j} → ℕ) (z t M d : ℕ) (Y r c : ℤ) :
    alignmentRetainedRepresentative M d
      (alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest t)) U) Y r c =
    alignmentRetainedRepresentative M d
      (alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest z)) U) Y r c := by
  rw [alignment_tail_rest_retained_product T U x j hj rest z t]

end Hindman168
