import Hindman168.ProductCosetQuotient
import Mathlib.Algebra.Group.Center

/-! The ACTUAL diagonal of the original center in G times G. Only this
subgroup, not the original lattice, is proved normal. -/

namespace Hindman168
variable (G : Type*) [Group G]

def diagonalCenterSubgroup : Subgroup (G × G) :=
  (Subgroup.center G).map ((MonoidHom.id G).prod (MonoidHom.id G))

theorem diagonal_center_mem_iff (p : G × G) :
    p ∈ diagonalCenterSubgroup G ↔ ∃ z : Subgroup.center G, p = ((z : G),(z : G)) := by
  constructor
  · rintro ⟨z,hz,hp⟩
    exact ⟨⟨z,hz⟩,hp.symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨(z : G),z.property,rfl⟩

theorem diagonal_center_le_center : diagonalCenterSubgroup G ≤ Subgroup.center (G × G) := by
  intro p hp
  obtain ⟨z,rfl⟩ := (diagonal_center_mem_iff G p).mp hp
  apply Subgroup.mem_center_iff.mpr
  intro q
  exact Prod.ext (Subgroup.mem_center_iff.mp z.property q.1)
    (Subgroup.mem_center_iff.mp z.property q.2)

theorem diagonal_center_normal : (diagonalCenterSubgroup G).Normal := by
  refine ⟨?_⟩
  intro a ha g
  have hc := diagonal_center_le_center G ha
  simpa only [Subgroup.mem_center_iff.mp hc g,mul_inv_cancel_right] using ha

theorem product_coset_map_diagonal_action (Γ : Subgroup G) (z : G) (q : (G × G) ⧸ Γ.prod Γ) :
    productCosetMap Γ Γ ((z,z) • q) =
      (z • (productCosetMap Γ Γ q).1,z • (productCosetMap Γ Γ q).2) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

end Hindman168
