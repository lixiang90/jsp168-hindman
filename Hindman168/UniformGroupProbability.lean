import Hindman168.UniformFiniteMass
import Hindman168.EventMass

/-!
# Uniform finite laws, coordinate domination and surjective group images

These identities concern the original finite probability coefficients.
Surjective group homomorphisms have equal-size fibers, proved explicitly
by multiplication, so they preserve uniform probability laws.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def uniformFintypeMass (α : Type*) [Fintype α] : Mass α :=
  uniformFinsetMass Finset.univ

theorem uniformFintypeMass_apply {α : Type*} [Fintype α] (x : α) :
    uniformFintypeMass α x = (Fintype.card α : ℝ)⁻¹ := by
  simp [uniformFintypeMass, uniformFinsetMass, flatMass_apply]

theorem uniformFintypeMass_nonneg (α : Type*) [Fintype α] (x : α) :
    0 ≤ uniformFintypeMass α x := uniformFinsetMass_nonneg _ x

theorem uniformFintypeMass_total (α : Type*) [Fintype α] [Nonempty α] :
    total (uniformFintypeMass α) = 1 :=
  uniformFinsetMass_total _ (by simpa using Fintype.card_pos)

theorem piUniformFintype_event {α : Type*} [Fintype α] (n : ℕ) (E : (Fin n → α) → Prop) :
    event (piMass (fun _ : Fin n => uniformFintypeMass α)) E =
      ((Finset.univ.filter E).card : ℝ) / (Fintype.card α : ℝ) ^ n := by
  rw [event_eq_sum _ E (Finset.subset_univ _)]
  simp only [piMass_apply, uniformFintypeMass_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← inv_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]

theorem event_piMass_domination {ι α : Type*} [Fintype ι] [Fintype α]
    (μ ν : ι → Mass α) (hμ : ∀ i a, 0 ≤ μ i a) {C : ℝ}
    (_hC : 0 ≤ C) (hcap : ∀ i a, μ i a ≤ C * ν i a) (E : (ι → α) → Prop) :
    event (piMass μ) E ≤ C ^ Fintype.card ι * event (piMass ν) E := by
  rw [event_eq_sum _ E (Finset.subset_univ _), event_eq_sum _ E (Finset.subset_univ _),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · rw [if_pos hx, if_pos hx, piMass_apply, piMass_apply]
    have h := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => hμ i (x i)) (fun i _ => hcap i (x i))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h
  · simp only [if_neg hx, mul_zero, le_refl]

theorem group_hom_fiber_card {G H : Type*} [Group G] [Group H] [Fintype G]
    (f : G →* H) (hf : Function.Surjective f) (h : H) :
    ((Finset.univ : Finset G).filter (fun g => f g = h)).card =
      ((Finset.univ : Finset G).filter (fun g => f g = 1)).card := by
  obtain ⟨g, hg⟩ := hf h
  symm
  apply Finset.card_bij (fun a _ => g * a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [map_mul, ha, mul_one, hg]
  · intro a _ b _ hab
    exact mul_left_cancel hab
  · intro b hb
    refine ⟨g⁻¹ * b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [map_mul, map_inv, hg, hb, inv_mul_cancel]

theorem uniformFintypeMass_group_push {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) :
    (uniformFintypeMass G).mapDomain f = uniformFintypeMass H := by
  let ρ := (uniformFintypeMass G).mapDomain f
  have hconst (h : H) : ρ h = ρ 1 := by
    unfold ρ uniformFintypeMass uniformFinsetMass
    rw [flatMass_push_coeff, flatMass_push_coeff, group_hom_fiber_card f hf h]
  have ht : total ρ = 1 := by rw [total_push]; exact uniformFintypeMass_total G
  have hc : (Fintype.card H : ℝ) * ρ 1 = 1 := by
    rw [total_eq_sum ρ (Finset.subset_univ _)] at ht
    simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using ht
  have hcard : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hv : ρ 1 = (Fintype.card H : ℝ)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hcard).mpr
    simpa only [mul_comm] using hc
  ext h
  rw [uniformFintypeMass_apply]
  exact (hconst h).trans hv

end Hindman168.FiniteMass
