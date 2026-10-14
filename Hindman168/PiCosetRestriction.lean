import Hindman168.PiCosetQuotient

/-! Restriction between genuine product coset spaces. No subgroup is assumed
normal, and no coset representative is chosen by the restriction map. -/
namespace Hindman168

variable {ι κ : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  (Γ : ∀ i, Subgroup (G i)) (index : κ → ι)

noncomputable def piCosetRestriction :
    (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ →
      (∀ k, G (index k)) ⧸ Subgroup.pi Set.univ (fun k => Γ (index k)) :=
  fun x => (piCosetEquiv (fun k => Γ (index k))).symm
    (fun k => piCosetMap Γ x (index k))

theorem piCosetRestriction_coordinate
    (x : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) (k : κ) :
    piCosetMap (fun k => Γ (index k)) (piCosetRestriction Γ index x) k =
      piCosetMap Γ x (index k) :=
  congrFun ((piCosetEquiv (fun k => Γ (index k))).apply_symm_apply _) k

theorem piCosetRestriction_mk (g : ∀ i, G i) :
    piCosetRestriction Γ index (g : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) =
      ((fun k => g (index k)) : (∀ k, G (index k)) ⧸
        Subgroup.pi Set.univ (fun k => Γ (index k))) := by
  apply (piCosetMap_bijective (fun k => Γ (index k))).1
  funext k
  rw [piCosetRestriction_coordinate]
  rfl

theorem piCosetRestriction_id
    (x : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) :
    piCosetRestriction Γ id x = x := by
  induction x using Quotient.inductionOn with
  | _ g => exact piCosetRestriction_mk Γ id g

theorem piCosetRestriction_comp {τ : Type*} (next : τ → κ)
    (x : (∀ i, G i) ⧸ Subgroup.pi Set.univ Γ) :
    piCosetRestriction (fun k => Γ (index k)) next
      (piCosetRestriction Γ index x) =
      piCosetRestriction Γ (index ∘ next) x := by
  induction x using Quotient.inductionOn with
  | _ g =>
    rw [piCosetRestriction_mk, piCosetRestriction_mk, piCosetRestriction_mk]
    rfl

variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

theorem piCosetRestriction_continuous : Continuous (piCosetRestriction Γ index) :=
  (piCosetHomeomorph (fun k => Γ (index k))).symm.continuous.comp
    (continuous_pi (fun k => (continuous_apply (index k)).comp
      (piCosetMap_continuous Γ)))

end Hindman168
