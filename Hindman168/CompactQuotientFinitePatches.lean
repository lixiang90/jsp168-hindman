import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.Compact

namespace Hindman168
open Set Topology
open scoped Classical

/-- Actual precompact injective patches with a finite image cover, obtained
from local injectivity and compactness of the ORIGINAL quotient. -/
theorem compact_quotient_finite_patches {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [CompactSpace Y] (f : X → Y) (hop : IsOpenMap f)
    (hsurj : Function.Surjective f) (hinj : IsLocallyInjective f) :
    ∃ m : ℕ, ∃ K : Fin m → Set X,
      (∀ i, IsCompact (K i) ∧ (interior (K i)).InjOn f) ∧
      ∀ y : Y, ∃ i, y ∈ f '' interior (K i) := by
  have hlocal : ∀ x : X, ∃ K : Set X, IsCompact K ∧ x ∈ interior K ∧ (interior K).InjOn f := by
    intro x
    obtain ⟨U, hU, hx, hUf⟩ := hinj x
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
    exact ⟨K, hK, hxK, hUf.mono (interior_subset.trans hKU)⟩
  choose K hK hxK hfK using hlocal
  have hcover : Set.univ ⊆ ⋃ x : X, f '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact mem_iUnion.mpr ⟨x, ⟨x, hxK x, rfl⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => f '' interior (K x))
    (fun x => hop _ isOpen_interior) hcover
  let e := (Fintype.equivFin ↥t).symm
  refine ⟨Fintype.card ↥t, (fun i => K (e i).val), (fun i => ⟨hK _, hfK _⟩), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := mem_iUnion.mp (ht (mem_univ y))
  obtain ⟨hxt, hy⟩ := mem_iUnion.mp hx
  refine ⟨e.symm ⟨x, hxt⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hy

end Hindman168
