import Hindman168.UniformGroupProbability
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.Basic

/-!
# Actual finite local kernel counts

Uniform mass pushed through a finite additive-group homomorphism is
uniform on its image. The probability of its zero fiber is therefore
the reciprocal of the image cardinality. Multiplying by the target
cardinality gives the normalized divisibility count, which is at least
one. The final specialization uses exactly the prime-power residue
groups and the normalization p^(sum of row valuations) in the paper.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem add_group_hom_fiber_card {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G]
    (f : G →+ H) (hf : Function.Surjective f) (h : H) :
    ((Finset.univ : Finset G).filter (fun g => f g = h)).card =
      ((Finset.univ : Finset G).filter (fun g => f g = 0)).card := by
  obtain ⟨g, hg⟩ := hf h
  symm
  apply Finset.card_bij (fun a _ => g + a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [map_add, ha, add_zero, hg]
  · intro a _ b _ hab
    exact add_left_cancel hab
  · intro b hb
    refine ⟨-g + b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [map_add, map_neg, hg, hb, neg_add_cancel]

theorem uniformFintypeMass_addGroup_push {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    (uniformFintypeMass G).mapDomain f = uniformFintypeMass H := by
  let ρ := (uniformFintypeMass G).mapDomain f
  have hconst (h : H) : ρ h = ρ 0 := by
    unfold ρ uniformFintypeMass uniformFinsetMass
    rw [flatMass_push_coeff, flatMass_push_coeff, add_group_hom_fiber_card f hf h]
  have ht : total ρ = 1 := by rw [total_push]; exact uniformFintypeMass_total G
  have hc : (Fintype.card H : ℝ) * ρ 0 = 1 := by
    rw [total_eq_sum ρ (Finset.subset_univ _)] at ht
    simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using ht
  have hcard : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hv : ρ 0 = (Fintype.card H : ℝ)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hcard).mpr
    simpa only [mul_comm] using hc
  ext h
  rw [uniformFintypeMass_apply]
  exact (hconst h).trans hv

theorem uniformFintypeMass_event_eq {α : Type*} [Fintype α] (a : α) :
    event (uniformFintypeMass α) (fun x => x = a) = (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [event_eq_sum _ _ (Finset.subset_univ _)]
  simp [uniformFintypeMass_apply]

theorem uniformFintypeMass_addHom_kernel {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) :
    event (uniformFintypeMass G) (fun x => f x = 0) = (Nat.card f.range : ℝ)⁻¹ := by
  classical
  letI : Fintype f.range := Fintype.ofFinite f.range
  have hpush := uniformFintypeMass_addGroup_push f.rangeRestrict f.rangeRestrict_surjective
  have hE : (fun x : G => f x = 0) = (fun x => f.rangeRestrict x = 0) := by
    funext x
    exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hE]
  have hmap := event_map (uniformFintypeMass G) f.rangeRestrict (fun y : f.range => y = 0)
  rw [hpush, uniformFintypeMass_event_eq] at hmap
  simpa only [Nat.card_eq_fintype_card] using hmap.symm

noncomputable def normalizedAddKernelMass {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) : ℝ :=
  (Fintype.card H : ℝ) * event (uniformFintypeMass G) (fun x => f x = 0)

theorem normalizedAddKernelMass_eq {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) :
    normalizedAddKernelMass f = (Fintype.card H : ℝ) / Nat.card f.range := by
  rw [normalizedAddKernelMass, uniformFintypeMass_addHom_kernel, div_eq_mul_inv]

theorem one_le_normalizedAddKernelMass {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) : 1 ≤ normalizedAddKernelMass f := by
  classical
  letI : Fintype f.range := Fintype.ofFinite f.range
  have hr : 0 < (Fintype.card f.range : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card f.range : ℝ) ≤ Fintype.card H := by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val : f.range → H) Subtype.val_injective
  rw [normalizedAddKernelMass_eq, Nat.card_eq_fintype_card]
  exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hc)

theorem normalizedAddKernelMass_le_card {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) : normalizedAddKernelMass f ≤ Fintype.card H := by
  unfold normalizedAddKernelMass
  have h := event_le_total (uniformFintypeMass G) (fun x => f x = 0) (uniformFintypeMass_nonneg G)
  rw [uniformFintypeMass_total G] at h
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (mul_one _)

theorem normalizedAddKernelMass_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    normalizedAddKernelMass f = 1 := by
  have hpush := uniformFintypeMass_addGroup_push f hf
  have h : event (uniformFintypeMass G) (fun x => f x = 0) = (Fintype.card H : ℝ)⁻¹ := by
    have hmap := event_map (uniformFintypeMass G) f (fun y : H => y = 0)
    rw [hpush, uniformFintypeMass_event_eq] at hmap
    exact hmap.symm
  rw [normalizedAddKernelMass, h]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem primePower_row_target_card (p q : ℕ) [NeZero p] (a : Fin q → ℕ) :
    Fintype.card (∀ u : Fin q, ZMod (p ^ a u)) = p ^ (∑ u, a u) := by
  rw [Fintype.card_pi]
  simp only [ZMod.card]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem primePower_normalized_kernel_bounds (p q d A : ℕ) [NeZero p] (a : Fin q → ℕ)
    (f : (Fin d → ZMod (p ^ A)) →+ (∀ u : Fin q, ZMod (p ^ a u))) :
    1 ≤ (p ^ (∑ u, a u) : ℕ) * event (uniformFintypeMass (Fin d → ZMod (p ^ A))) (fun x => f x = 0) ∧
    (p ^ (∑ u, a u) : ℕ) * event (uniformFintypeMass (Fin d → ZMod (p ^ A))) (fun x => f x = 0) ≤
      (p ^ (∑ u, a u) : ℕ) := by
  have h1 := one_le_normalizedAddKernelMass f
  have h2 := normalizedAddKernelMass_le_card f
  unfold normalizedAddKernelMass at h1 h2
  rw [primePower_row_target_card p q a] at h1 h2
  exact ⟨h1, h2⟩

end Hindman168
