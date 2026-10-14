import Hindman168.NilUpperFaceFiltration
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Genuine image and inverse-image group filtrations, preserving the
actual commutator conditions. -/

namespace Hindman168
open scoped commutatorElement
variable {G K : Type*} [Group G] [Group K]

theorem CubeGroupFiltration.comap {F : ℕ → Subgroup K}
    (hF : CubeGroupFiltration F) (f : G →* K) :
    CubeGroupFiltration (fun i => (F i).comap f) := by
  refine ⟨fun i j hij => Subgroup.comap_mono (hF.antitone hij),?_⟩
  intro i j g hg k hk
  change f ⁅g,k⁆ ∈ F (i+j)
  rw [map_commutatorElement]
  exact hF.commutator_mem i j _ hg _ hk

theorem CubeGroupFiltration.map {F : ℕ → Subgroup G}
    (hF : CubeGroupFiltration F) (f : G →* K) :
    CubeGroupFiltration (fun i => (F i).map f) := by
  refine ⟨fun i j hij => Subgroup.map_mono (hF.antitone hij),?_⟩
  intro i j g hg k hk
  obtain ⟨x,hx,rfl⟩ := hg
  obtain ⟨y,hy,rfl⟩ := hk
  exact ⟨⁅x,y⁆,hF.commutator_mem i j _ hx _ hy,map_commutatorElement f x y⟩

theorem subgroup_filtration_quotient_terminal (F : ℕ → Subgroup G)
    (N : Subgroup G) [N.Normal] (d : ℕ) (hd : F d ≤ N) :
    (F d).map (QuotientGroup.mk' N) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨y,hy,rfl⟩
  change QuotientGroup.mk' N y = 1
  exact (QuotientGroup.eq_one_iff y).mpr (hd hy)

end Hindman168
