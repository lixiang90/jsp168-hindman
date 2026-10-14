import Hindman168.UpperFaceLieFiltration

/-! Splitting an actual face proves the level-bracket annihilation
required by section 7, including empty faces and zero-dimensional cubes. -/
namespace Hindman168
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

theorem finite_face_split {α : Type*} [DecidableEq α] (D : Finset α) (a b : ℕ)
    (hD : D.card ≤ a+b) :
    ∃ A B : Finset α, A ⊆ D ∧ B ⊆ D ∧ A ∪ B = D ∧ A.card ≤ a ∧ B.card ≤ b := by
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq (s := D) (Nat.min_le_right a D.card)
  refine ⟨A,D \ A,hA,Finset.sdiff_subset,?_,?_,?_⟩
  · exact Finset.union_sdiff_of_subset hA
  · rw [hcard]
    exact Nat.min_le_left _ _
  · rw [Finset.card_sdiff_of_subset hA,hcard]
    omega

theorem upper_face_character_bracket {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] (F : ℕ → Submodule R L) (hF : Antitone F) (d : ℕ)
    (chi : (Finset (Fin d) → L) →ₗ[R] R)
    (hKill : ∀ x ∈ upperFaceLieLayer F d 0, ∀ y ∈ upperFaceLieLayer F d 0,
      chi ⁅x,y⁆ = 0)
    (D : Finset (Fin d)) (a b : ℕ) (hD : D.card ≤ a+b)
    (x y : L) (hx : x ∈ F a) (hy : y ∈ F b) :
    chi (upperFaceLieArray (R := R) D ⁅x,y⁆) = 0 := by
  obtain ⟨A,B,_,_,hAB,hA,hB⟩ := finite_face_split D a b hD
  have hxA : upperFaceLieArray (R := R) A x ∈ upperFaceLieLayer F d 0 :=
    upper_face_lie_layer_generator F d 0 A x (by
      change x ∈ F A.card
      exact hF hA hx)
  have hyB : upperFaceLieArray (R := R) B y ∈ upperFaceLieLayer F d 0 :=
    upper_face_lie_layer_generator F d 0 B y (by
      change y ∈ F B.card
      exact hF hB hy)
  have he := hKill _ hxA _ hyB
  rw [upper_face_lie_array_bracket,hAB] at he
  exact he

end Hindman168
