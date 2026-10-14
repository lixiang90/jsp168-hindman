import Hindman168.DiscreteSubgroupCompactIntersection
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Group

/-! Actual quotient lattice elements in an image of a relatively compact
original set have finitely many representatives after adjustment by an
actual intersection lattice. No discreteness of the quotient image is
assumed: it is obtained from actual discrete compact intersections in G. -/

namespace Hindman168
open Function Set
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 theorem normalQuotient_lattice_image_inter_finite (Γ N : Subgroup G) [N.Normal]
    [DiscreteTopology Γ] {C K O : Set G} (hC : IsCompact C) (hCN : C ⊆ N)
    (hcover : (N : Set G) ⊆ C * (Γ ⊓ N : Subgroup G))
    (hK : IsCompact K) (hOK : O ⊆ K) :
    {y : G ⧸ N | y ∈ Γ.map (QuotientGroup.mk' N) ∧
      y ∈ (QuotientGroup.mk : G → G ⧸ N) '' O}.Finite := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hfinite := (discreteSubgroup_compact_inter_finite Γ (hK.mul hC)).image q
  apply hfinite.subset
  rintro y ⟨hyΓ, o, ho, hoy⟩
  obtain ⟨γ, hγ, hγy⟩ := hyΓ
  have hqeq : (QuotientGroup.mk o : G ⧸ N) = QuotientGroup.mk γ := hoy.trans hγy.symm
  have hn : o⁻¹ * γ ∈ N := QuotientGroup.eq.mp hqeq
  obtain ⟨c, hc, δ, hδ, he⟩ := mem_mul.mp (hcover hn)
  have hoc : o * c = γ * δ⁻¹ := by
    have he' := congrArg (fun x : G => o * x * δ⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using he'
  have hocΓ : o * c ∈ Γ := by rw [hoc]; exact Γ.mul_mem hγ (Γ.inv_mem hδ.1)
  have hocK : o * c ∈ K * C := mem_mul.mpr ⟨o, hOK ho, c, hc, rfl⟩
  refine ⟨o * c, ⟨hocΓ, hocK⟩, ?_⟩
  have hqc : q c = 1 := (QuotientGroup.eq_one_iff c).mpr (hCN hc)
  rw [map_mul, hqc, mul_one]
  exact hoy

end Hindman168
