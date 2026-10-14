import Hindman168.SubgroupRealCharacterConjugation
import Hindman168.NilLowerCentralCommutator

/-! A TRUE character kernel inside an actual subgroup contains the
original group derived subgroup when every original commutator vanishes. -/
namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem subgroup_real_character_derived_zero (N : Subgroup G) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y)=ψ x+ψ y)
    (hcomm : ∀ g h : G, ⁅g,h⁆ ∈ N)
    (hzero : ∀ g h : G, ψ (subgroupCommElement N hcomm g h)=0)
    (g : G) (hg : g ∈ N) (hderived : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ψ ⟨g,hg⟩ = 0 := by
  let q : N →* Multiplicative ℝ :=
    { toFun := fun x => Multiplicative.ofAdd (ψ x)
      map_one' := subgroup_real_character_one N ψ hψ
      map_mul' := hψ }
  let K := q.ker.map N.subtype
  have hK : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ K := by
    rw [Subgroup.top_lowerCentralSeries_one,commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    refine ⟨subgroupCommElement N hcomm x y,?_,rfl⟩
    change ψ (subgroupCommElement N hcomm x y)=0
    exact hzero x y
  obtain ⟨x,hx,hxg⟩ := hK hderived
  have he : x = ⟨g,hg⟩ := Subtype.ext hxg
  rw [he] at hx
  exact hx

end Hindman168
