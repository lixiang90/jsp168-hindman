import Hindman168.AlignmentTailRestTuple

/-! Literal tail insertion preserves actual original retained products and
CubeScale, for every subset of T. No pivot value or exposure key is assumed. -/
namespace Hindman168
open scoped BigOperators

theorem alignment_tail_tuple_original_product {N : ℕ} (T U : Finset (Fin N))
    (hU : U ⊆ T) (x y : Fin N → ℕ) :
    alignmentNaturalBlockProduct (alignmentTailTuple T x (fun k : T => y k.val)) U=
      alignmentNaturalBlockProduct y U := by
  apply Finset.prod_congr rfl
  intro k hk
  exact alignment_tail_tuple_inside T x (fun k : T => y k.val) (⟨k,hU hk⟩ : T)

theorem alignment_tail_tuple_original_cube_scale {N : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin N) (T : Finset (Fin N)) (x y : Fin N → ℕ) :
    alignmentCubeScale F w i T (alignmentTailTuple T x (fun k : T => y k.val))=
      alignmentCubeScale F w i T y := by
  unfold alignmentCubeScale alignmentShortBinVolume
  congr 3
  apply Finset.prod_congr rfl
  intro k hk
  rw [alignment_tail_tuple_inside T x (fun k : T => y k.val) (⟨k,hk⟩ : T)]

end Hindman168
