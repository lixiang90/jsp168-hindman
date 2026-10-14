import Hindman168.NilUpperFaceReflection
import Mathlib.Data.Finset.SymmDiff

/-! Reflecting all Boolean coordinates is complementation. Consequently
actual quotient cubes with trivial top filtration layer have a unique
missing root as well as a unique missing top. No normality of the lattice
subgroup is assumed. -/

namespace Hindman168
open scoped Classical symmDiff

variable {G : Type*} [Group G] {d : ℕ}

theorem cubeFlip_eq_symmDiff (j : Fin d) (E : Finset (Fin d)) :
    cubeFlip j E = E ∆ {j} := by
  ext k
  by_cases hj : j ∈ E <;> by_cases hk : k = j <;>
    simp [cubeFlip, Finset.mem_symmDiff, hj, hk]

theorem cubeReflectList_eq_symmDiff (js : List (Fin d)) (hjs : js.Nodup)
    (E : Finset (Fin d)) : cubeReflectList js E = E ∆ js.toFinset := by
  induction js with
  | nil => exact (symmDiff_bot E).symm
  | cons j js ih =>
    obtain ⟨hj, ht⟩ := List.nodup_cons.mp hjs
    rw [cubeReflectList, cubeFlip_eq_symmDiff, ih ht, symmDiff_assoc]
    have hs : js.toFinset ∆ {j} = insert j js.toFinset := by
      ext k
      have hjsj : j ∉ js.toFinset := by simpa using hj
      by_cases hk : k = j <;> simp [Finset.mem_symmDiff, hjsj, hk]
    rw [hs, List.toFinset_cons]

theorem cubeReflectList_all_eq_compl (E : Finset (Fin d)) :
    cubeReflectList ((Finset.univ : Finset (Fin d)).toList) E = Eᶜ := by
  rw [cubeReflectList_eq_symmDiff _ (Finset.nodup_toList _), Finset.toList_toFinset]
  exact symmDiff_top E

theorem upperFaceCubeGroup_complement_mem (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    (fun E => z Eᶜ) ∈ upperFaceCubeGroup F d := by
  have hp := upperFaceCubeGroup_reflectList_mem F hF
    ((Finset.univ : Finset (Fin d)).toList) z hz
  simpa only [cubeReflectList_all_eq_compl] using hp

theorem upperFaceCubeGroup_coset_missing_root (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    (x y : Finset (Fin d) → G) (hx : x ∈ upperFaceCubeGroup F d)
    (hy : y ∈ upperFaceCubeGroup F d)
    (hpartial : ∀ E, E.Nonempty → (x E : G ⧸ Γ) = (y E : G ⧸ Γ)) :
    (x ∅ : G ⧸ Γ) = (y ∅ : G ⧸ Γ) := by
  let xr : Finset (Fin d) → G := fun E => x Eᶜ
  let yr : Finset (Fin d) → G := fun E => y Eᶜ
  have hx' : xr ∈ upperFaceCubeGroup F d := upperFaceCubeGroup_complement_mem F hF x hx
  have hy' : yr ∈ upperFaceCubeGroup F d := upperFaceCubeGroup_complement_mem F hF y hy
  have hc := upperFaceCubeGroup_coset_corner_unique F hF htop Γ
  have heq := hc (cosetCornerCube Γ xr) ⟨xr, hx', rfl⟩
    (cosetCornerCube Γ yr) ⟨yr, hy', rfl⟩ (by
      intro E
      change (x E.valᶜ : G ⧸ Γ) = (y E.valᶜ : G ⧸ Γ)
      apply hpartial
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      exact E.property (by simpa only [Finset.compl_eq_empty_iff] using h))
  simpa only [cosetCornerCube, xr, yr, Finset.compl_univ] using heq

end Hindman168
