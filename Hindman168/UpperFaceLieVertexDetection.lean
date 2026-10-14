import Hindman168.UpperFaceLieCoordinates

/-! A filtered Lie cube vanishing on all proper subvertices has its value
at V in the original layer |V|. This is actual triangular recovery. -/
namespace Hindman168
open scoped BigOperators
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {d : ℕ}

theorem upper_face_lie_vertex_layer (F : ℕ → Submodule R L)
    (x : Finset (Fin d) → L) (hx : x ∈ upperFaceLieLayer F d 0)
    (V : Finset (Fin d)) (hz : ∀ U, U ⊂ V → x U = 0) : x V ∈ F V.card := by
  classical
  obtain ⟨a,⟨ha,hax⟩,_⟩ := upper_face_lie_layer_coordinates F 0 x hx
  have hcoeff (U : Finset (Fin d)) : U ⊂ V → a U = 0 := by
    refine Finset.strongInductionOn U ?_
    intro U ih hUV
    have hs : (∑ W ∈ U.powerset, a W) = a U := by
      apply Finset.sum_eq_single U
      · intro W hW hne
        have hWU : W ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hW,hne⟩
        exact ih W hWU (hWU.trans hUV)
      · simp
    have he := upper_face_lie_sum_vertex (R := R) a U
    rw [hax, hz U hUV, hs] at he
    exact he.symm
  have hs : (∑ U ∈ V.powerset, a U) = a V := by
    apply Finset.sum_eq_single V
    · intro U hU hne
      exact hcoeff U (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hU,hne⟩)
    · simp
  have he := upper_face_lie_sum_vertex (R := R) a V
  rw [hax,hs] at he
  rw [he]
  exact ha V

end Hindman168
