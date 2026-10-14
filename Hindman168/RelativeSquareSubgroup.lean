import Hindman168.NilUpperFaceFiltration
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Actual relative squares of original subgroups. Original lattice
normality is not required; only the comparison subgroup is normal. -/

namespace Hindman168
variable {G : Type*} [Group G]

def relativeDiagonalSubgroup (H : Subgroup G) : Subgroup (G × G) :=
  H.map ((MonoidHom.id G).prod (MonoidHom.id G))

def relativeSquareSubgroup (H N : Subgroup G) [N.Normal] : Subgroup (G × G) :=
  H.prod H ⊓ ((QuotientGroup.mk' N).comp (MonoidHom.fst G G)).eqLocus
    ((QuotientGroup.mk' N).comp (MonoidHom.snd G G))

theorem relative_square_mem_iff (H N : Subgroup G) [N.Normal] (p : G × G) :
    p ∈ relativeSquareSubgroup H N ↔ p.1 ∈ H ∧ p.2 ∈ H ∧ p.2⁻¹ * p.1 ∈ N := by
  change (p.1 ∈ H ∧ p.2 ∈ H) ∧ QuotientGroup.mk' N p.1 = QuotientGroup.mk' N p.2 ↔ _
  rw [(QuotientGroup.mk' N).eq_iff,QuotientGroup.ker_mk']
  exact and_assoc

theorem relative_diagonal_mem_iff (H : Subgroup G) (p : G × G) :
    p ∈ relativeDiagonalSubgroup H ↔ p.1 ∈ H ∧ p.1 = p.2 := by
  constructor
  · rintro ⟨g,hg,hp⟩
    change (g,g) = p at hp
    cases hp
    exact ⟨hg,rfl⟩
  · rintro ⟨hp,he⟩
    refine ⟨p.1,hp,?_⟩
    exact Prod.ext rfl he

theorem relative_square_le_product (H N : Subgroup G) [N.Normal] :
    relativeSquareSubgroup H N ≤ H.prod H := inf_le_left

theorem relative_diagonal_le_square (H N : Subgroup G) [N.Normal] :
    relativeDiagonalSubgroup H ≤ relativeSquareSubgroup H N := by
  intro p hp
  obtain ⟨h1,he⟩ := (relative_diagonal_mem_iff H p).mp hp
  apply (relative_square_mem_iff H N p).mpr
  exact ⟨h1,he ▸ h1,by rw [← he,inv_mul_cancel]; exact N.one_mem⟩

theorem relative_square_mono {H K N M : Subgroup G} [N.Normal] [M.Normal]
    (hHK : H ≤ K) (hNM : N ≤ M) :
    relativeSquareSubgroup H N ≤ relativeSquareSubgroup K M := by
  intro p hp
  obtain ⟨h1,h2,h3⟩ := (relative_square_mem_iff H N p).mp hp
  exact (relative_square_mem_iff K M p).mpr ⟨hHK h1,hHK h2,hNM h3⟩

theorem relative_square_bot (H : Subgroup G) :
    relativeSquareSubgroup H ⊥ = relativeDiagonalSubgroup H := by
  ext p
  rw [relative_square_mem_iff,relative_diagonal_mem_iff,Subgroup.mem_bot,inv_mul_eq_one]
  constructor
  · rintro ⟨h1,_,he⟩
    exact ⟨h1,he.symm⟩
  · rintro ⟨h1,he⟩
    exact ⟨h1,he ▸ h1,he.symm⟩

theorem relative_square_decomposition (H N : Subgroup G) [N.Normal]
    (p : relativeSquareSubgroup H N) :
    ∃ e : N, ∃ b : H, (p : G × G) = ((b : G),(b : G)) * ((e : G),1) := by
  obtain ⟨_,h2,h3⟩ := (relative_square_mem_iff H N p.val).mp p.property
  refine ⟨⟨p.val.2⁻¹ * p.val.1,h3⟩,⟨p.val.2,h2⟩,?_⟩
  apply Prod.ext
  · change p.val.1 = p.val.2 * (p.val.2⁻¹ * p.val.1)
    rw [mul_inv_cancel_left]
  · change p.val.2 = p.val.2 * 1
    rw [mul_one]

end Hindman168
