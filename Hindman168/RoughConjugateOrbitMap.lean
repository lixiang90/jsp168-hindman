import Hindman168.RoughConjugateLatticeTopology

namespace Hindman168
open Topology

variable {G : Type*} [Group G]

noncomputable def roughConjugateOrbitMap (Γ L : Subgroup G) (g ell : G) :
    L ⧸ (roughConjugateSubgroup Γ g).comap L.subtype → G ⧸ Γ :=
  Quotient.lift (fun h : L => (QuotientGroup.mk (ell * h.val * g) : G ⧸ Γ))
    (fun x y h => by
      apply QuotientGroup.eq.mpr
      have hsub : x⁻¹*y ∈ (roughConjugateSubgroup Γ g).comap L.subtype :=
        QuotientGroup.leftRel_apply.mp h
      have hh : x.val⁻¹ * y.val ∈ roughConjugateSubgroup Γ g := hsub
      have he : (ell*x.val*g)⁻¹*(ell*y.val*g) = g⁻¹*(x.val⁻¹*y.val)*g := by group
      rw [he]
      exact (roughConjugateSubgroup_mem_iff Γ g _).mp hh)

theorem roughConjugateOrbitMap_mk (Γ L : Subgroup G) (g ell : G) (h : L) :
    roughConjugateOrbitMap Γ L g ell (QuotientGroup.mk h) =
      (QuotientGroup.mk (ell * h.val * g) : G ⧸ Γ) := rfl

theorem roughConjugateOrbitMap_injective (Γ L : Subgroup G) (g ell : G) :
    Function.Injective (roughConjugateOrbitMap Γ L g ell) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    intro h
    have hh : (ell*x.val*g)⁻¹*(ell*y.val*g) ∈ Γ := QuotientGroup.eq.mp h
    apply QuotientGroup.eq.mpr
    change x.val⁻¹*y.val ∈ roughConjugateSubgroup Γ g
    apply (roughConjugateSubgroup_mem_iff Γ g _).mpr
    convert hh using 1
    group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem roughConjugateOrbitMap_continuous (Γ L : Subgroup G) (g ell : G) :
    Continuous (roughConjugateOrbitMap Γ L g ell) := by
  apply continuous_quot_lift
  exact QuotientGroup.continuous_mk.comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem roughConjugateOrbitMap_joint_continuous (Γ L : Subgroup G) (g : G) :
    Continuous (fun p : G × (L ⧸ (roughConjugateSubgroup Γ g).comap L.subtype) =>
      roughConjugateOrbitMap Γ L g p.1 p.2) := by
  have he : (fun p : G × (L ⧸ (roughConjugateSubgroup Γ g).comap L.subtype) =>
      roughConjugateOrbitMap Γ L g p.1 p.2) =
      (fun p => p.1 • roughConjugateOrbitMap Γ L g 1 p.2) := by
    funext p
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective p.2
    rw [← hh]
    simp only [roughConjugateOrbitMap_mk, one_mul]
    exact congrArg (fun h : G => (QuotientGroup.mk h : G ⧸ Γ)) (mul_assoc p.1 h.val g)
  rw [he]
  exact continuous_fst.smul ((roughConjugateOrbitMap_continuous Γ L g 1).comp continuous_snd)

theorem roughConjugateOrbitMap_closedEmbedding (Γ L : Subgroup G) (g ell : G)
    [T2Space (G ⧸ Γ)] [CompactSpace (L ⧸ (roughConjugateSubgroup Γ g).comap L.subtype)] :
    IsClosedEmbedding (roughConjugateOrbitMap Γ L g ell) :=
  (roughConjugateOrbitMap_continuous Γ L g ell).isClosedEmbedding
    (roughConjugateOrbitMap_injective Γ L g ell)

end Hindman168
