import Hindman168.NilUpperFaceFiltration
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! A concrete increasing-cardinality order of every Boolean upper face,
with no duplicate faces. Every suffix is upward closed under inclusion,
which is the exact property needed for subgroup collection. -/

namespace Hindman168
open scoped Classical

noncomputable def orderedCubeFaces (d : ℕ) : List (Finset (Fin d)) :=
  ((Finset.univ : Finset (Finset (Fin d))).toList).mergeSort
    (fun D E => decide (D.card ≤ E.card))

theorem orderedCubeFaces_mem (d : ℕ) (D : Finset (Fin d)) : D ∈ orderedCubeFaces d := by
  rw [orderedCubeFaces, List.mem_mergeSort]
  simp

theorem orderedCubeFaces_nodup (d : ℕ) : (orderedCubeFaces d).Nodup := by
  apply List.nodup_mergeSort.mpr
  exact Finset.nodup_toList _

theorem orderedCubeFaces_pairwise (d : ℕ) :
    (orderedCubeFaces d).Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E) := by
  have hcard : (orderedCubeFaces d).Pairwise (fun D E => D.card ≤ E.card) := by
    simpa only [orderedCubeFaces, decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun D E : Finset (Fin d) => decide (D.card ≤ E.card))
      (fun _ _ _ h1 h2 => by simpa using le_trans (by simpa using h1) (by simpa using h2))
      (fun D E => by simpa using le_total D.card E.card)
      ((Finset.univ : Finset (Finset (Fin d))).toList)
  exact hcard.and (orderedCubeFaces_nodup d)

theorem orderedCubeFaces_tailClosed (d : ℕ) : UpperFaceTailClosed (orderedCubeFaces d) := by
  intro E _ D _
  exact orderedCubeFaces_mem d D

theorem upperFaceTailClosed_tail {d : ℕ} (D : Finset (Fin d))
    (faces : List (Finset (Fin d)))
    (horder : (D :: faces).Pairwise (fun E V => E.card ≤ V.card ∧ E ≠ V))
    (hclosed : UpperFaceTailClosed (D :: faces)) : UpperFaceTailClosed faces := by
  intro E hE V hEV
  have hv := hclosed E (by simp [hE]) V hEV
  rcases List.mem_cons.mp hv with rfl | hV
  · have hp := (List.pairwise_cons.mp horder).1 E hE
    exact False.elim (hp.2 (Finset.eq_of_subset_of_card_le hEV hp.1).symm)
  · exact hV

variable {G : Type*} [Group G] {d : ℕ}

noncomputable def upperFaceProduct (a : Finset (Fin d) → G)
    (faces : List (Finset (Fin d))) : Finset (Fin d) → G :=
  (faces.map (fun D => upperFaceArray D (a D))).prod

theorem upperFaceProduct_apply (a : Finset (Fin d) → G)
    (faces : List (Finset (Fin d))) (E : Finset (Fin d)) :
    upperFaceProduct a faces E = upperFaceValue a faces E := by
  rw [upperFaceProduct, Pi.list_prod_apply]
  simp only [upperFaceValue, triangularFaceValue, List.map_map, upperFaceArray, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro D _
  by_cases hD : D ⊆ E <;> simp [hD]

theorem upperFaceProduct_cons (a : Finset (Fin d) → G)
    (D : Finset (Fin d)) (faces : List (Finset (Fin d))) :
    upperFaceProduct a (D :: faces) = upperFaceArray D (a D) * upperFaceProduct a faces := by
  simp [upperFaceProduct]

theorem upperFaceProduct_update_outside (a : Finset (Fin d) → G)
    (D : Finset (Fin d)) (g : G) (faces : List (Finset (Fin d))) (hD : D ∉ faces) :
    upperFaceProduct (Function.update a D g) faces = upperFaceProduct a faces := by
  unfold upperFaceProduct
  congr 1
  apply List.map_congr_left
  intro E hE
  rw [Function.update_of_ne (by intro h; exact hD (h ▸ hE))]

end Hindman168
