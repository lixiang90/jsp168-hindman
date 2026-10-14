import Hindman168.CentralCommutatorRecords
import Hindman168.DiscreteSubgroupCompactIntersection
import Hindman168.FiniteCoordinateRecords
import Mathlib.Topology.Algebra.Group.Basic

/-! For central products k*gamma with k in an actual compact set and
gamma in an actual discrete subgroup, commutator records on any finite
set of subgroup elements have finite image. Compactness and discreteness
are used on the actual original-group values of every coordinate. -/

namespace Hindman168
open Set
open scoped commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 theorem discreteSubgroup_central_commutator_image_finite (Γ : Subgroup G)
    [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) {s : G} (hs : s ∈ Γ) :
    ((fun γ : G => ⁅γ, s⁆) '' {γ : G | γ ∈ Γ ∧ ∃ k ∈ K, k * γ ∈ Subgroup.center G}).Finite := by
  have hcont : Continuous (fun k : G => ⁅k⁻¹, s⁆) := by
    simp only [commutatorElement_def]
    fun_prop
  apply (discreteSubgroup_compact_inter_finite Γ (hK.image hcont)).subset
  rintro y ⟨γ, ⟨hγ, k, hk, hc⟩, rfl⟩
  refine ⟨?_, k, hk, ?_⟩
  · simp only [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hγ hs) (Γ.inv_mem hγ)) (Γ.inv_mem hs)
  · exact (commutator_eq_of_mul_mem_center hc s).symm

 theorem discreteSubgroup_central_finite_records (Γ : Subgroup G) [DiscreteTopology Γ]
    {K S : Set G} (hK : IsCompact K) (hS : S.Finite) (hSΓ : S ⊆ Γ) :
    ((fun γ : G => fun s : S => ⁅γ, (s : G)⁆) ''
      {γ : G | γ ∈ Γ ∧ ∃ k ∈ K, k * γ ∈ Subgroup.center G}).Finite := by
  letI : Finite S := hS
  apply finite_image_of_finite_coordinate_images
  intro s
  exact discreteSubgroup_central_commutator_image_finite Γ hK (hSΓ s.property)

end Hindman168
