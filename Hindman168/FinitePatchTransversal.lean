import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Finset.Max

namespace Hindman168
open Set MeasureTheory
open scoped Classical

def finitePatchStratum {X Y : Type*} {m : ℕ} (f : X → Y) (U : Fin m → Set X) (i : Fin m) : Set X :=
  U i \ f ⁻¹' (⋃ j ∈ Finset.Iio i, f '' U j)

def finitePatchTransversal {X Y : Type*} {m : ℕ} (f : X → Y) (U : Fin m → Set X) : Set X :=
  ⋃ i, finitePatchStratum f U i

theorem finite_patch_stratum_mem {X Y : Type*} {m : ℕ} (f : X → Y) (U : Fin m → Set X)
    (i : Fin m) (x : X) : x ∈ finitePatchStratum f U i ↔
      x ∈ U i ∧ ∀ j : Fin m, j < i → f x ∉ f '' U j := by
  simp only [finitePatchStratum, mem_sdiff, mem_preimage, mem_iUnion,
    Finset.mem_Iio, not_exists]

theorem finite_patch_transversal_measurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    {m : ℕ} (f : X → Y) (U : Fin m → Set X) (hf : Continuous f) (hop : IsOpenMap f)
    (hU : ∀ i, IsOpen (U i)) : MeasurableSet (finitePatchTransversal f U) := by
  apply MeasurableSet.iUnion
  intro i
  have hV : IsOpen (⋃ j ∈ Finset.Iio i, f '' U j) := isOpen_biUnion (fun j _ => hop _ (hU j))
  exact (hU i).measurableSet.diff (hV.measurableSet.preimage hf.measurable)

theorem finite_patch_transversal_subset {X Y : Type*} {m : ℕ} (f : X → Y) (U K : Fin m → Set X)
    (hUK : ∀ i, U i ⊆ K i) : finitePatchTransversal f U ⊆ ⋃ i, K i := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, hUK i ((finite_patch_stratum_mem f U i x).mp hi).1⟩

theorem finite_patch_transversal_injective {X Y : Type*} {m : ℕ} (f : X → Y) (U : Fin m → Set X)
    (hU : ∀ i, (U i).InjOn f) : (finitePatchTransversal f U).InjOn f := by
  intro x hx y hy he
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  obtain ⟨hxi, hix⟩ := (finite_patch_stratum_mem f U i x).mp hi
  obtain ⟨hyj, hjy⟩ := (finite_patch_stratum_mem f U j y).mp hj
  have hij : i=j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim (hjy i hlt ⟨x, hxi, he⟩)
    · exact heq
    · exact False.elim (hix j hgt ⟨y, hyj, he.symm⟩)
  subst j
  exact hU i hxi hyj he

theorem finite_patch_transversal_surjective {X Y : Type*} {m : ℕ} (f : X → Y) (U : Fin m → Set X)
    (hcover : ∀ y, ∃ i, y ∈ f '' U i) : ∀ y, ∃ x ∈ finitePatchTransversal f U, f x = y := by
  intro y
  let s := Finset.univ.filter (fun i => y ∈ f '' U i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hcover y
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := s.min' hs
  have hi : y ∈ f '' U i := (Finset.mem_filter.mp (s.min'_mem hs)).2
  obtain ⟨x, hx, hxy⟩ := hi
  refine ⟨x, mem_iUnion.mpr ⟨i, (finite_patch_stratum_mem f U i x).mpr ⟨hx, ?_⟩⟩, hxy⟩
  intro j hji hj
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxy ▸ hj⟩
  exact (not_le_of_gt hji) (s.min'_le j hjs)

end Hindman168
