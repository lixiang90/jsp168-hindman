import Hindman168.SubgroupLatticeQuotient
import Mathlib.Tactic.Group

namespace Hindman168

variable {G : Type*} [Group G]

def roughConjugateSubgroup (Γ : Subgroup G) (g : G) : Subgroup G :=
  Γ.map (MulAut.conj g).toMonoidHom

theorem roughConjugateSubgroup_mem (Γ : Subgroup G) (g h : G) :
    g * h * g⁻¹ ∈ roughConjugateSubgroup Γ g ↔ h ∈ Γ := by
  change (MulAut.conj g) h ∈ Γ.map (MulAut.conj g).toMonoidHom ↔ h ∈ Γ
  constructor
  · intro hh
    obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp hh
    exact (MulAut.conj g).injective he ▸ hk
  · intro hh
    exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩

theorem roughConjugateSubgroup_mem_iff (Γ : Subgroup G) (g h : G) :
    h ∈ roughConjugateSubgroup Γ g ↔ g⁻¹ * h * g ∈ Γ := by
  constructor
  · intro hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    change g⁻¹ * (g*k*g⁻¹) * g ∈ Γ
    convert hk using 1
    group
  · intro hh
    have he : g * (g⁻¹*h*g) * g⁻¹ = h := by group
    rw [← he]
    exact (roughConjugateSubgroup_mem Γ g _).mpr hh

noncomputable def roughConjugateQuotientMap (Γ : Subgroup G) (g : G) :
    G ⧸ Γ → G ⧸ roughConjugateSubgroup Γ g :=
  Quotient.lift (fun x : G => (QuotientGroup.mk ((MulAut.conj g) x) : G ⧸ roughConjugateSubgroup Γ g))
    (fun x y h => by
      apply QuotientGroup.eq.mpr
      change ((MulAut.conj g) x)⁻¹ * (MulAut.conj g) y ∈ Γ.map (MulAut.conj g).toMonoidHom
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map.mpr ⟨x⁻¹*y, QuotientGroup.leftRel_apply.mp h, rfl⟩)

theorem roughConjugateQuotientMap_surjective (Γ : Subgroup G) (g : G) :
    Function.Surjective (roughConjugateQuotientMap Γ g) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, rfl⟩ := (MulAut.conj g).surjective x
  exact ⟨QuotientGroup.mk y, rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def roughConjugateSubgroupHomeomorph (Γ : Subgroup G) (g : G) :
    Γ ≃ₜ roughConjugateSubgroup Γ g where
  toEquiv := ((MulAut.conj g).subgroupMap Γ).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem roughConjugateSubgroup_discrete (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) :
    DiscreteTopology (roughConjugateSubgroup Γ g) :=
  (roughConjugateSubgroupHomeomorph Γ g).discreteTopology

theorem roughConjugateQuotientMap_continuous (Γ : Subgroup G) (g : G) :
    Continuous (roughConjugateQuotientMap Γ g) := by
  apply continuous_quot_lift
  exact QuotientGroup.continuous_mk.comp ((continuous_const.mul continuous_id).mul continuous_const)

theorem roughConjugateSubgroup_quotient_compact (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] (g : G) :
    CompactSpace (G ⧸ roughConjugateSubgroup Γ g) :=
  (roughConjugateQuotientMap_surjective Γ g).compactSpace (roughConjugateQuotientMap_continuous Γ g)

end Hindman168
