import Hindman168.NativeNilmanifoldData
import Hindman168.OpenMapCompactRepresentatives
import Hindman168.NativeLatticeFiniteGeneration

/-! ONE FIXED compact original group set supplies actual representatives
for ALL original nonnormal lattice cosets. No coordinate box or spatial
Lipschitz estimate is assumed. -/

namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_exists_compact_coset_representatives {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) :
    ∃ K : Set D.G, IsCompact K ∧ ∀ g : D.G, ∃ r ∈ K, ∃ γ : D.Γ, g = r * γ := by
  letI : LocallyCompactSpace D.G := nativeLieGroup_locallyCompact (E := D.E) (I := D.I) (G := D.G)
  obtain ⟨K,O,hK,_,hOK,hq⟩ := exists_compact_open_representatives
    (QuotientGroup.isOpenMap_coe (N := D.Γ)) (QuotientGroup.mk_surjective (s := D.Γ))
  refine ⟨K,hK,?_⟩
  intro g
  obtain ⟨r,hr,he⟩ := (hq.symm ▸ Set.mem_univ (QuotientGroup.mk g : D.G ⧸ D.Γ))
  have hg : r⁻¹ * g ∈ D.Γ := QuotientGroup.eq.mp he
  refine ⟨r,hOK hr,⟨r⁻¹*g,hg⟩,?_⟩
  exact (mul_inv_cancel_left _ _).symm

end Hindman168
