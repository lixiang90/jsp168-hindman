import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.OpenQuotient

/-! An actual open surjection from a locally compact space
onto a compact space has compact representatives with an open subset
already mapping onto the entire target. The construction uses actual
compact neighborhoods and a genuine finite subcover. -/

namespace Hindman168
open Set Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

 theorem exists_compact_open_representatives [LocallyCompactSpace X] [CompactSpace Y]
    {f : X → Y} (ho : IsOpenMap f) (hs : Surjective f) :
    ∃ K O : Set X, IsCompact K ∧ IsOpen O ∧ O ⊆ K ∧ f '' O = univ := by
  classical
  choose K hK hKn using fun x : X => exists_compact_mem_nhds x
  have hcover : (univ : Set Y) ⊆ ⋃ x : X, f '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    exact mem_iUnion.mpr ⟨x, mem_image_of_mem f (mem_interior_iff_mem_nhds.mpr (hKn x))⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => f '' interior (K x)) (fun x => ho _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, K x, ⋃ x ∈ s, interior (K x), ?_, ?_, ?_, ?_⟩
  · exact s.finite_toSet.isCompact_biUnion (fun x _ => hK x)
  · exact isOpen_iUnion (fun x => isOpen_iUnion (fun _ => isOpen_interior))
  · intro x hx
    obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨a, ha, interior_subset hx⟩
  · apply eq_univ_of_forall
    intro y
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact mem_image_of_mem f (mem_iUnion₂.mpr ⟨x, hx, hz⟩)

end Hindman168
