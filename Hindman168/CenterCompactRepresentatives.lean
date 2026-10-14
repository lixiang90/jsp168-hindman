import Hindman168.DiscreteCentralCommutatorRecords
import Hindman168.ConnectedSubgroupOverlapGeneration
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Group

/-! Actual compact representatives for the center modulo its intersection
with a specified discrete finitely generated subgroup whose centralizer
is the center. Finite commutator records reduce the original compact
representatives to finitely many translates, then a closed intersection. -/

namespace Hindman168
open Function Set
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 theorem center_isClosed : IsClosed (Subgroup.center G : Set G) := by
  rw [← Subgroup.centralizer_univ]
  exact Set.isClosed_centralizer _

 theorem exists_compact_center_representatives (Γ : Subgroup G) [DiscreteTopology Γ]
    (hfg : Γ.FG) (hcentral : Subgroup.centralizer (Γ : Set G) = Subgroup.center G)
    {K : Set G} (hK : IsCompact K) (hcover : K * (Γ : Set G) = univ) :
    ∃ C : Set G, IsCompact C ∧ C ⊆ Subgroup.center G ∧
      (Subgroup.center G : Set G) ⊆ C * (Γ ⊓ Subgroup.center G : Subgroup G) := by
  classical
  obtain ⟨S, hgen, hS⟩ := Γ.fg_iff.mp hfg
  have hSΓ : S ⊆ Γ := by rw [← hgen]; exact Subgroup.subset_closure
  let T : Set G := {γ : G | γ ∈ Γ ∧ ∃ k ∈ K, k * γ ∈ Subgroup.center G}
  let r : G → S → G := fun γ s => ⁅γ, (s : G)⁆
  have hr : (r '' T).Finite := discreteSubgroup_central_finite_records Γ hK hS hSΓ
  obtain ⟨D, hDT, hD, hrD⟩ := exists_finite_image_representatives T r hr
  let U : Set G := ⋃ δ ∈ D, (fun k : G => k * δ) '' K
  let C : Set G := U ∩ (Subgroup.center G : Set G)
  have hU : IsCompact U := hD.isCompact_biUnion fun δ _ =>
    hK.image (continuous_id.mul continuous_const)
  refine ⟨C, hU.inter_right center_isClosed, fun _ h => h.2, ?_⟩
  intro c hc
  have hcK : c ∈ K * (Γ : Set G) := by rw [hcover]; trivial
  obtain ⟨k, hk, γ, hγ, he⟩ := mem_mul.mp hcK
  have hγT : γ ∈ T := ⟨hγ, k, hk, he ▸ hc⟩
  have hrγ : r γ ∈ r '' D := by rw [hrD]; exact ⟨γ, hγT, rfl⟩
  obtain ⟨δ, hδ, hrδ⟩ := hrγ
  let z : G := δ⁻¹ * γ
  have hzΓ : z ∈ Γ := Γ.mul_mem (Γ.inv_mem (hDT hδ).1) hγ
  have hzC : z ∈ Subgroup.center G := by
    rw [← hcentral]
    apply inv_mul_mem_centralizer_of_commutator_records_eq Γ hgen
    intro s hs
    exact (congrFun hrδ ⟨s, hs⟩).symm
  have hkd : k * δ = c * z⁻¹ := by rw [← he]; dsimp [z]; group
  have hkdC : k * δ ∈ Subgroup.center G := by
    rw [hkd]
    exact (Subgroup.center G).mul_mem hc ((Subgroup.center G).inv_mem hzC)
  refine mem_mul.mpr ⟨k * δ, ⟨?_, hkdC⟩, z, ⟨hzΓ, hzC⟩, ?_⟩
  · exact mem_iUnion.mpr ⟨δ, mem_iUnion.mpr ⟨hδ, k, hk, rfl⟩⟩
  · dsimp [z]
    simpa only [mul_assoc, mul_inv_cancel_left] using he

 theorem exists_compact_center_subtype_representatives (Γ : Subgroup G) [DiscreteTopology Γ]
    (hfg : Γ.FG) (hcentral : Subgroup.centralizer (Γ : Set G) = Subgroup.center G)
    {K : Set G} (hK : IsCompact K) (hcover : K * (Γ : Set G) = univ) :
    ∃ D : Set (Subgroup.center G), IsCompact D ∧
      D * (Γ.subgroupOf (Subgroup.center G) : Set (Subgroup.center G)) = univ := by
  obtain ⟨C, hC, _, hrep⟩ := exists_compact_center_representatives Γ hfg hcentral hK hcover
  let D : Set (Subgroup.center G) := ((↑) : Subgroup.center G → G) ⁻¹' C
  refine ⟨D, center_isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hC, ?_⟩
  apply eq_univ_of_forall
  intro c
  obtain ⟨d, hd, z, hz, he⟩ := mem_mul.mp (hrep c.property)
  have hdcenter : d ∈ Subgroup.center G := by
    have hdz : d = (c : G) * z⁻¹ := by rw [← he]; simp
    rw [hdz]
    exact (Subgroup.center G).mul_mem c.property ((Subgroup.center G).inv_mem hz.2)
  exact mem_mul.mpr ⟨⟨d, hdcenter⟩, hd, ⟨z, hz.2⟩, hz.1, Subtype.ext he⟩

end Hindman168
