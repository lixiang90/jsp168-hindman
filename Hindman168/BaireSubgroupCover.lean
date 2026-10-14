import Hindman168.SigmaCompactGeneratedSubgroup
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

/-! A sigma-compact subgroup whose countably many homeomorphic images
cover a Baire group is open. In a connected group it is the whole group. -/

namespace Hindman168
open Set Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [BaireSpace G]

theorem sigmaCompact_subgroup_open_of_homeomorph_cover
    (H : Subgroup G) (hH : IsSigmaCompact (H : Set G)) (e : ℕ → G ≃ₜ G)
    (hcover : ∀ x : G, ∃ n, x ∈ e n '' (H : Set G)) : IsOpen (H : Set G) := by
  obtain ⟨K, hK, hKH⟩ := hH
  have hsub : ∀ n, K n ⊆ (H : Set G) := by
    intro n x hx
    rw [← hKH]
    exact mem_iUnion.mpr ⟨n, hx⟩
  let C : ℕ × ℕ → Set G := fun p => e p.1 '' K p.2
  have hc : ∀ p, IsClosed (C p) := fun p => ((hK p.2).image (e p.1).continuous).isClosed
  have hu : ⋃ p, C p = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, y, hy, rfl⟩ := hcover x
    rw [← hKH] at hy
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨(n, m), y, hm, rfl⟩
  obtain ⟨p, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hc hu
  let U := (e p.1).symm '' interior (C p)
  have hU : IsOpen U := (e p.1).symm.isOpenMap _ isOpen_interior
  have hUH : U ⊆ (H : Set G) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := interior_subset hy
    simpa only [Homeomorph.symm_apply_apply] using hsub p.2 hw
  exact H.isOpen_of_mem_nhds
    (Filter.mem_of_superset (hU.mem_nhds ⟨x, hx, rfl⟩) hUH)

theorem sigmaCompact_subgroup_eq_top_of_homeomorph_cover [ConnectedSpace G]
    (H : Subgroup G) (hH : IsSigmaCompact (H : Set G)) (e : ℕ → G ≃ₜ G)
    (hcover : ∀ x : G, ∃ n, x ∈ e n '' (H : Set G)) : H = ⊤ := by
  have ho := sigmaCompact_subgroup_open_of_homeomorph_cover H hH e hcover
  have hu : (H : Set G) = univ :=
    IsClopen.eq_univ ⟨H.isClosed_of_isOpen ho, ho⟩ ⟨1, H.one_mem⟩
  exact SetLike.coe_injective hu

end Hindman168
