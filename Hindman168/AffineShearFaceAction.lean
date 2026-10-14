import Hindman168.UpperFaceLieVertexDetection
import Hindman168.NilUpperFaceGroup

/-! The codimension-one face test in Proposition 7.5.  A genuine face action
on the cube space forces its linear part to act trivially on the associated
graded.  No filtration-preservation or graded-identity premise is used. -/
namespace Hindman168

attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

noncomputable def affineShearFaceAction {G : Type*} {d : ℕ}
    (j : Fin d) (f : G → G) (z : Finset (Fin d) → G) : Finset (Fin d) → G :=
  fun V => if j ∈ V then f (z V) else z V

section Linear
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {d : ℕ}

 theorem affineShearFaceAction_linear_difference (A : L →ₗ[R] L)
    (j : Fin d) (D : Finset (Fin d)) (x : L) :
    affineShearFaceAction j A (upperFaceLieArray (R := R) D x) -
      upperFaceLieArray (R := R) D x =
      upperFaceLieArray (R := R) (insert j D) (A x - x) := by
  classical
  funext V
  by_cases hj : j ∈ V <;> by_cases hD : D ⊆ V <;>
    simp [affineShearFaceAction, upperFaceLieArray, Finset.insert_subset_iff, hj, hD]

 theorem affineShearFaceAction_forces_layer (F : ℕ → Submodule R L)
    (A : L →ₗ[R] L) (j : Fin d)
    (hA : ∀ z ∈ upperFaceLieLayer F d 0,
      affineShearFaceAction j A z ∈ upperFaceLieLayer F d 0)
    (D : Finset (Fin d)) (hj : j ∉ D) (x : L) (hx : x ∈ F D.card) :
    A x - x ∈ F (D.card + 1) := by
  classical
  have hz : upperFaceLieArray (R := R) D x ∈ upperFaceLieLayer F d 0 :=
    upper_face_lie_layer_generator F d 0 D x (by simpa using hx)
  have hd := (upperFaceLieLayer F d 0).sub_mem (hA _ hz) hz
  rw [affineShearFaceAction_linear_difference] at hd
  have htop := upper_face_lie_vertex_layer F
    (upperFaceLieArray (R := R) (insert j D) (A x - x)) hd (insert j D) (by
      intro V hV
      have hn : ¬ insert j D ⊆ V := fun h => (Finset.ssubset_iff_subset_ne.mp hV).2
        (Finset.Subset.antisymm (Finset.ssubset_iff_subset_ne.mp hV).1 h)
      simp [upperFaceLieArray, hn])
  simpa [upperFaceLieArray, Finset.card_insert_of_notMem hj] using htop

 theorem affineShearFaceAction_forces_graded_identity (F : ℕ → Submodule R L)
    (A : L →ₗ[R] L) (i : ℕ)
    (hA : ∀ z ∈ upperFaceLieLayer F (i+1) 0,
      affineShearFaceAction (Fin.last i) A z ∈ upperFaceLieLayer F (i+1) 0)
    (x : L) (hx : x ∈ F i) : A x - x ∈ F (i+1) := by
  classical
  let D : Finset (Fin (i+1)) := Finset.univ.erase (Fin.last i)
  have hcard : D.card = i := by simp [D]
  have h := affineShearFaceAction_forces_layer F A (Fin.last i) hA D
    (by simp [D]) x (by simpa [hcard] using hx)
  simpa [hcard] using h

end Linear

section Group
variable {G : Type*} [Group G] {d : ℕ}

 theorem affineShearFaceAction_remove_translation (j : Fin d) (c : G)
    (φ : G →* G) (z : Finset (Fin d) → G) :
    (affineShearFaceAction j (fun y => c * φ y) (1 : Finset (Fin d) → G))⁻¹ *
      affineShearFaceAction j (fun y => c * φ y) z =
      affineShearFaceAction j φ z := by
  classical
  funext V
  by_cases hj : j ∈ V <;> simp [affineShearFaceAction, hj]

 theorem affineShearFaceAction_linearPart_mem (C : Subgroup (Finset (Fin d) → G))
    (j : Fin d) (c : G) (φ : G →* G)
    (h : ∀ z ∈ C, affineShearFaceAction j (fun y => c * φ y) z ∈ C)
    (z : Finset (Fin d) → G) (hz : z ∈ C) :
    affineShearFaceAction j φ z ∈ C := by
  rw [← affineShearFaceAction_remove_translation j c φ z]
  exact C.mul_mem (C.inv_mem (h 1 C.one_mem)) (h z hz)

 theorem affineShear_cube_vertex_initial (F : ℕ → Subgroup G) (hF : Antitone F)
    (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d)
    (V : Finset (Fin d)) : z V ∈ F 0 := by
  classical
  let ev : (Finset (Fin d) → G) →* G :=
    { toFun := fun x => x V, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hle : upperFaceCubeGroup F d ≤ (F 0).comap ev := by
    apply (Subgroup.closure_le (K := (F 0).comap ev)).mpr
    rintro _ ⟨A, g, hg, rfl⟩
    change (if A ⊆ V then g else 1) ∈ F 0
    split_ifs
    · exact hF (Nat.zero_le A.card) hg
    · exact (F 0).one_mem
  exact hle hz

end Group
end Hindman168
