import Hindman168.NilCornerCubeCertificate
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! The paper's actual upper-face generated cube subgroup. All linear
orbit cubes belong to it, for arbitrary group elements, base points and
integer exponents, using constant and codimension-one generators only.
This does not require a Lie-theoretic factorization or bounded orbits. -/

namespace Hindman168
open scoped BigOperators Classical

variable {G : Type*} [Group G] {d : ℕ}

noncomputable def upperFaceArray (D : Finset (Fin d)) (g : G) : Finset (Fin d) → G :=
  fun E => if D ⊆ E then g else 1

noncomputable def upperFaceCubeGroup (F : ℕ → Subgroup G) (d : ℕ) :
    Subgroup (Finset (Fin d) → G) :=
  Subgroup.closure {v | ∃ D : Finset (Fin d), ∃ g ∈ F D.card, v = upperFaceArray D g}

theorem upperFaceArray_mem_cubeGroup (F : ℕ → Subgroup G) (D : Finset (Fin d))
    (g : G) (hg : g ∈ F D.card) : upperFaceArray D g ∈ upperFaceCubeGroup F d := by
  exact Subgroup.subset_closure ⟨D, g, hg, rfl⟩

theorem upperFaceArray_empty (g : G) :
    upperFaceArray (∅ : Finset (Fin d)) g = fun _ => g := by
  funext E
  simp [upperFaceArray]

theorem list_same_base_zpow_product (g : G) (b : List ℤ) :
    (b.map (fun n => g ^ n)).prod = g ^ b.sum := by
  induction b with
  | nil => simp
  | cons n b ih => simp [ih, zpow_add]

theorem upperFace_linear_direction_product (g : G) (b : Fin d → ℤ)
    (E : Finset (Fin d)) :
    (List.ofFn (fun j : Fin d => upperFaceArray {j} (g ^ b j))).prod E =
      g ^ (∑ j ∈ E, b j) := by
  rw [Pi.list_prod_apply, List.map_ofFn]
  have hfun : (fun j : Fin d => upperFaceArray {j} (g ^ b j) E) =
      (fun j => g ^ (if j ∈ E then b j else 0)) := by
    funext j
    by_cases hj : j ∈ E <;> simp [upperFaceArray, hj]
  dsimp only [Function.comp_def]
  have hm : List.ofFn (fun j : Fin d => g ^ (if j ∈ E then b j else 0)) =
      (List.ofFn (fun j : Fin d => if j ∈ E then b j else 0)).map (fun n => g ^ n) := by
    rw [List.map_ofFn]
    rfl
  rw [hfun, hm, list_same_base_zpow_product]
  simp [List.sum_ofFn]

theorem upperFace_linear_orbit_cube_mem (F : ℕ → Subgroup G)
    (hzero : F 0 = ⊤) (hone : F 1 = ⊤) (g x : G) (b₀ : ℤ) (b : Fin d → ℤ) :
    (fun E : Finset (Fin d) => g ^ (b₀ + ∑ j ∈ E, b j) * x) ∈ upperFaceCubeGroup F d := by
  have hc (z : G) : upperFaceArray (∅ : Finset (Fin d)) z ∈ upperFaceCubeGroup F d := by
    apply upperFaceArray_mem_cubeGroup
    simpa only [Finset.card_empty, hzero] using (Subgroup.mem_top z)
  have hdir : (List.ofFn (fun j : Fin d => upperFaceArray {j} (g ^ b j))).prod ∈
      upperFaceCubeGroup F d := by
    apply (upperFaceCubeGroup F d).list_prod_mem
    intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    apply upperFaceArray_mem_cubeGroup
    simpa only [Finset.card_singleton, hone] using (Subgroup.mem_top (g ^ b j))
  have hprod := (upperFaceCubeGroup F d).mul_mem
    ((upperFaceCubeGroup F d).mul_mem (hc (g ^ b₀)) hdir) (hc x)
  convert hprod using 1
  funext E
  simp only [Pi.mul_apply, upperFaceArray_empty, upperFace_linear_direction_product,
    zpow_add, mul_assoc]

end Hindman168
