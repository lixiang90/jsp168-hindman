import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.LocallyCompact

/-! A compact quotient of a weakly locally compact space under an open
surjection has a compact set of representatives. No continuous section or
normal subgroup is assumed. -/

namespace Hindman168
open Set Topology
open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem openSurjection_compact_representatives [WeaklyLocallyCompactSpace X]
    [CompactSpace Y] (π : X → Y) (hπ : IsOpenMap π) (hsurj : Function.Surjective π) :
    ∃ K : Set X, IsCompact K ∧ π '' K = Set.univ := by
  choose K hc hn using fun x : X => exists_compact_mem_nhds x
  have hcover : (Set.univ : Set Y) ⊆ ⋃ x, π '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hn x), rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => π '' interior (K x)) (fun _ => hπ _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, K x, ?_, ?_⟩
  · exact s.finite_toSet.isCompact_biUnion (fun x _ => hc x)
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx, z, hz, heq⟩ := mem_iUnion₂.mp (hs (Set.mem_univ y))
    exact ⟨z, mem_iUnion₂.mpr ⟨x, hx, interior_subset hz⟩, heq⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

theorem compactQuotient_lattice_representatives [WeaklyLocallyCompactSpace G]
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ k ∈ K, ∃ γ ∈ Γ, g = k * γ := by
  obtain ⟨K, hc, hK⟩ := openSurjection_compact_representatives
    ((↑) : G → G ⧸ Γ) QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective
  refine ⟨K, hc, ?_⟩
  intro g
  have hg : (g : G ⧸ Γ) ∈ ((↑) : G → G ⧸ Γ) '' K := by rw [hK]; trivial
  obtain ⟨k, hk, heq⟩ := hg
  refine ⟨k, hk, k⁻¹ * g, QuotientGroup.eq.mp heq, ?_⟩
  simp only [mul_inv_cancel_left]

omit [SeparatelyContinuousMul G] in
theorem compactSpace_of_lattice_representatives (Γ : Subgroup G) (K : Set G)
    (hc : IsCompact K) (hrep : ∀ g : G, ∃ k ∈ K, ∃ γ ∈ Γ, g = k * γ) :
    CompactSpace (G ⧸ Γ) := by
  have himage : ((↑) : G → G ⧸ Γ) '' K = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, γ, hγ, rfl⟩ := hrep g
    refine ⟨k, hk, QuotientGroup.eq.mpr ?_⟩
    simpa only [inv_mul_cancel_left] using hγ
  exact isCompact_univ_iff.mp (himage ▸ hc.image QuotientGroup.continuous_mk)

end Hindman168
