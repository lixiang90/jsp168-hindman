import Hindman168.NilpotentArbitraryPositiveRoots

/-! In a finitely generated nilpotent group, a uniform positive power
inside an ARBITRARY subgroup gives a finite quotient by its normal core.
The subgroup itself is never assumed normal. -/
namespace Hindman168
open Subgroup

theorem uniform_power_mem_normalCore {G : Type*} [Group G] (H : Subgroup G)
    (N : ℕ) (h : ∀ g : G, g^N ∈ H) (g : G) : g^N ∈ H.normalCore := by
  intro b
  simpa only [conj_pow] using h (b*g*b⁻¹)

theorem nilpotent_fg_uniform_power_core_finite {G : Type*} [Group G]
    [Group.IsNilpotent G] [Group.FG G] (H : Subgroup G)
    (N : ℕ) (hN : 0 < N) (h : ∀ g : G, g^N ∈ H) : Finite (G ⧸ H.normalCore) := by
  apply nilpotent_finite_of_fg_torsion
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective H.normalCore x
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨N,hN,?_⟩
  exact ((QuotientGroup.mk' H.normalCore).map_pow g N).symm.trans
    ((QuotientGroup.eq_one_iff (g^N)).mpr (uniform_power_mem_normalCore H N h g))

end Hindman168
