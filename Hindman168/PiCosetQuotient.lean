import Hindman168.ProductCosetQuotient

namespace Hindman168

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] (Γ : ∀ i, Subgroup (G i))

def piCosetMap : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ → ∀ i, G i ⧸ Γ i :=
  Quotient.lift (fun g i => (g i : G i ⧸ Γ i)) (by
    intro g h hgh
    funext i
    apply QuotientGroup.eq.mpr
    exact (Subgroup.mem_pi Set.univ).mp (QuotientGroup.leftRel_apply.mp hgh) i (Set.mem_univ i))

theorem piCosetMap_mk (g : ∀ i, G i) (i : ι) :
    piCosetMap Γ (g : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) i = (g i : G i ⧸ Γ i) := rfl

theorem piCosetMap_bijective : Function.Bijective (piCosetMap Γ) := by
  constructor
  · intro a b hab
    induction a, b using Quotient.inductionOn₂ with
    | _ g h =>
      apply QuotientGroup.eq.mpr
      apply (Subgroup.mem_pi Set.univ).mpr
      intro i _
      exact QuotientGroup.eq.mp (congrFun hab i)
  · intro a
    refine ⟨QuotientGroup.mk (fun i => (a i).out), ?_⟩
    funext i
    exact Quotient.out_eq (a i)

noncomputable def piCosetEquiv : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ ≃ ∀ i, G i ⧸ Γ i :=
  Equiv.ofBijective (piCosetMap Γ) (piCosetMap_bijective Γ)

variable [∀ i, TopologicalSpace (G i)]

theorem piCosetMap_continuous : Continuous (piCosetMap Γ) := by
  apply continuous_quot_lift
  exact continuous_pi (fun i => QuotientGroup.continuous_mk.comp (continuous_apply i))

variable [∀ i, IsTopologicalGroup (G i)]

theorem piCosetEquiv_symm_continuous : Continuous (piCosetEquiv Γ).symm := by
  let p : (∀ i, G i) → ∀ i, G i ⧸ Γ i := fun g i => (g i : G i ⧸ Γ i)
  have hp : IsOpenQuotientMap p := IsOpenQuotientMap.piMap
    (fun _ => QuotientGroup.isOpenQuotientMap_mk)
  apply hp.continuous_comp_iff.mp
  have he : (piCosetEquiv Γ).symm ∘ p = QuotientGroup.mk (s := Subgroup.pi Set.univ Γ) :=
    funext (fun g => (piCosetEquiv Γ).symm_apply_apply (QuotientGroup.mk g))
  rw [he]
  exact QuotientGroup.continuous_mk

noncomputable def piCosetHomeomorph : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ ≃ₜ ∀ i, G i ⧸ Γ i where
  toEquiv := piCosetEquiv Γ
  continuous_toFun := piCosetMap_continuous Γ
  continuous_invFun := piCosetEquiv_symm_continuous Γ

theorem piCoset_quotient_compact [∀ i, CompactSpace (G i ⧸ Γ i)] :
    CompactSpace ((∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) :=
  (piCosetHomeomorph Γ).symm.compactSpace

end Hindman168
