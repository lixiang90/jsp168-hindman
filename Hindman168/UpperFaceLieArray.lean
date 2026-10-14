import Hindman168.PointwiseLieAlgebra
import Mathlib.Data.Finset.Card

/-! Exact upper-face Lie arrays, including the empty face. -/
namespace Hindman168
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

noncomputable def upperFaceLieArray {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] {d : ℕ} (D : Finset (Fin d)) : L →ₗ⁅R⁆ (Finset (Fin d) → L) := by
  classical
  exact {
    toFun := fun x V => if D ⊆ V then x else 0
    map_add' := by intro x y; funext V; by_cases h : D ⊆ V <;> simp [h]
    map_smul' := by intro r x; funext V; by_cases h : D ⊆ V <;> simp [h]
    map_lie' := by
      intro x y
      funext V
      change (if D ⊆ V then ⁅x,y⁆ else 0) = ⁅(if D ⊆ V then x else 0),(if D ⊆ V then y else 0)⁆
      by_cases h : D ⊆ V <;> simp [h] }

theorem upper_face_lie_array_bracket {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] {d : ℕ} (D E : Finset (Fin d)) (x y : L) :
    ⁅upperFaceLieArray (R := R) D x,upperFaceLieArray (R := R) E y⁆ =
      upperFaceLieArray (R := R) (D ∪ E) ⁅x,y⁆ := by
  classical
  funext V
  change ⁅(if D ⊆ V then x else 0),(if E ⊆ V then y else 0)⁆ =
    (if D ∪ E ⊆ V then ⁅x,y⁆ else 0)
  by_cases hD : D ⊆ V <;> by_cases hE : E ⊆ V <;>
    simp [hD,hE,Finset.union_subset_iff]

theorem upper_face_lie_array_injective {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] {d : ℕ} (D : Finset (Fin d)) :
    Function.Injective (upperFaceLieArray (R := R) (L := L) D) := by
  intro x y h
  have hv := congrFun h D
  simpa [upperFaceLieArray] using hv

end Hindman168
