import Hindman168.PrincipalCoordinateProducts

/-! Subset products and their harmonic laws survive principal-index
relabeling exactly. The tail law is not postulated or renormalized. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

noncomputable def principalSubsetImageEquiv {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (S : Finset (Fin n)) : S ≃ S.image (energyPrincipal e) :=
  Equiv.ofBijective (fun k => ⟨energyPrincipal e k.val,
    Finset.mem_image.mpr ⟨k.val, k.property, rfl⟩⟩) (by
    constructor
    · intro k l h
      exact Subtype.ext ((energyPrincipal_strictMono e).injective (congrArg Subtype.val h))
    · intro j
      obtain ⟨k, hk, he⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨k, hk⟩, Subtype.ext he⟩)

theorem principalSubsetImageEquiv_val {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (S : Finset (Fin n)) (k : S) :
    (principalSubsetImageEquiv e S k).val = energyPrincipal e k.val := rfl

noncomputable def principalTailMass {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (S : Finset (Fin n)) (w : ℕ) : Mass ℕ :=
  (piMass (fun k : S => rawMass (F.cutoff w (energyPrincipal e k.val)) (primorial w))).mapDomain
    (fun x => ∏ k, x k)

theorem principalTailMass_image {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) (S : Finset (Fin n)) (w : ℕ) :
    principalTailMass e F S w = tailMass (primorial w)
      (List.ofFn (fun j : Fin (S.image (energyPrincipal e)).card =>
        F.cutoff w ((S.image (energyPrincipal e)).orderIsoOfFin rfl j))) := by
  let E := principalSubsetImageEquiv e S
  have hr := congrArg (fun μ : Mass (S → ℕ) => μ.mapDomain (fun x => ∏ k, x k))
    (piMass_reindex (fun j : S.image (energyPrincipal e) => rawMass (F.cutoff w j.val) (primorial w)) E)
  rw [← Finsupp.mapDomain_comp] at hr
  have hp : (piMass (fun j : S.image (energyPrincipal e) =>
      rawMass (F.cutoff w j.val) (primorial w))).mapDomain (fun x => ∏ j, x j) =
      principalTailMass e F S w := by
    refine (Finsupp.mapDomain_congr (fun x _ => ?_)).trans hr
    exact (Fintype.prod_equiv E (fun k => x (E k)) (fun j => x j) (fun _ => rfl)).symm
  rw [← hp]
  exact piMass_raw_product_equiv ((S.image (energyPrincipal e)).orderIsoOfFin rfl).toEquiv _ _

def principalSubsetProduct {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℕ) : ℕ :=
  ∏ k ∈ S, x k

theorem principalSubsetProduct_lift {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (S : Finset (Fin n)) (x : Fin M → ℕ) :
    (∏ j : S.image (energyPrincipal e),
      x ⟨j.val, Finset.mem_range.mp (selectedPrincipal_image_range e heM S j.property)⟩) =
      principalSubsetProduct S (fun k => x (selectedPrincipalIndex e heM k)) := by
  let f : ℕ → ℕ := fun j => if hj : j < M then x ⟨j, hj⟩ else 0
  have hprod : (∏ j : S.image (energyPrincipal e),
      x ⟨j.val, Finset.mem_range.mp (selectedPrincipal_image_range e heM S j.property)⟩) =
      ∏ j ∈ S.image (energyPrincipal e), f j := by
    rw [← Finset.prod_coe_sort (S.image (energyPrincipal e)) f]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [f]
    rw [dif_pos (Finset.mem_range.mp (selectedPrincipal_image_range e heM S j.property))]
  rw [hprod, Finset.prod_image (energyPrincipal_strictMono e).injective.injOn]
  apply Finset.prod_congr rfl
  intro k _
  dsimp only [f, selectedPrincipalIndex]
  rw [dif_pos (show energyPrincipal e k < M from heM _)]

end Hindman168
