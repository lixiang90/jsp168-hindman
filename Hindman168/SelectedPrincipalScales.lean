import Hindman168.SelectedPrincipalRawLaw

/-! The selected subset scale is the product of the actual selected
individual scales. The original common modulus and W^w factors remain. -/

namespace Hindman168
open scoped BigOperators Classical

noncomputable def selectedSubsetScale {n : ℕ} (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (w : ℕ) (S : Finset (Fin n)) : ℕ :=
  ∏ k ∈ S, masterScale (primorial w) w M {energyPrincipal e k}

theorem selectedPrincipal_image_range {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (S : Finset (Fin n)) :
    S.image (energyPrincipal e) ⊆ Finset.range M := by
  intro j hj
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr (heM _)

theorem selectedSubsetScale_eq_master {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (S : Finset (Fin n)) :
    selectedSubsetScale M e w S = masterScale (primorial w) w M (S.image (energyPrincipal e)) := by
  unfold selectedSubsetScale
  calc
    _ = ∏ k ∈ S, (primorial w) ^ (w * 2 ^ (M-1-energyPrincipal e k)) := by
      apply Finset.prod_congr rfl
      intro k _
      have h := masterScale_product (primorial w) w
        (show ({energyPrincipal e k} : Finset ℕ) ⊆ Finset.range M from by
          intro j hj
          have hj' := Finset.mem_singleton.mp hj
          subst j
          exact Finset.mem_range.mpr (heM _))
      simpa only [Finset.prod_singleton] using h.symm
    _ = _ := by
      rw [← masterScale_product (primorial w) w (selectedPrincipal_image_range e heM S)]
      rw [Finset.prod_image (energyPrincipal_strictMono e).injective.injOn]

theorem selectedSubsetScale_positive {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (S : Finset (Fin n)) :
    0 < selectedSubsetScale M e w S := by
  rw [selectedSubsetScale_eq_master e heM]
  exact Nat.pow_pos (primorial_pos w)

theorem selectedSubsetScale_power_dvd {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (primorial w) ^ w ∣ selectedSubsetScale M e w S := by
  rw [selectedSubsetScale_eq_master e heM]
  exact power_dvd_masterScale _ _ (hS.image _)

theorem MasterParameterConditions.selected_subset_scale_bound {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (S : Finset (Fin n)) :
    selectedSubsetScale M e w S ∣ (F.modulus w : ℕ) ∧
      selectedSubsetScale M e w S ≤ (F.modulus w : ℕ) := by
  rw [selectedSubsetScale_eq_master e heM]
  exact ⟨hF.subset_scale_dvd w _ (selectedPrincipal_image_range e heM S),
    hF.subset_scale_le w _ (selectedPrincipal_image_range e heM S)⟩

theorem selectedPrincipal_addsTo {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (P T : Finset (Fin n)) (j i : Fin n) (hP : P.Nonempty)
    (hPT : ∀ p ∈ P, ∀ t ∈ T, p < t) (hTj : ∀ t ∈ T, t < j) (hji : j < i) :
    Chain.AddsTo (P.image (energyPrincipal e)) (energyPrincipal e j)
      (T.image (energyPrincipal e)) (energyPrincipal e i) := by
  refine ⟨hP.image _, ?_, ?_, (energyPrincipal_strictMono e) hji⟩
  · intro p hp t ht
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    exact (energyPrincipal_strictMono e) (hPT p' hp' t' ht')
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    exact (energyPrincipal_strictMono e) (hTj t' ht')

theorem MasterParameterConditions.selected_adding_scales {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (P T : Finset (Fin n)) (j i : Fin n)
    (hP : P.Nonempty) (hT : T.Nonempty)
    (hPT : ∀ p ∈ P, ∀ t ∈ T, p < t) (hTj : ∀ t ∈ T, t < j) (hji : j < i) :
    selectedSubsetScale M e w (insert i T) * (primorial w) ^ w ∣
      selectedSubsetScale M e w (insert j P) := by
  rw [selectedSubsetScale_eq_master e heM, selectedSubsetScale_eq_master e heM,
    Finset.image_insert, Finset.image_insert]
  exact hF.adding_scales w _ _ _ _ (selectedPrincipal_addsTo e P T j i hP hPT hTj hji)
    (hT.image _) (by simpa only [Finset.image_insert] using
      selectedPrincipal_image_range e heM (insert j P))
    (by simpa only [Finset.image_insert] using
      selectedPrincipal_image_range e heM (insert i T))

end Hindman168
