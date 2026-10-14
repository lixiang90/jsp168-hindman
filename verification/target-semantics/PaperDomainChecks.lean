import Hindman168.FinalStrongFromNativeInverse
open Hindman168
open scoped BigOperators Classical
abbrev PosNat := {n : ℕ // 0 < n}
def posSum {m : ℕ} (a : Fin m → PosNat) (S : Finset (Fin m)) (hne : S.Nonempty) : PosNat :=
  ⟨∑ i ∈ S, (a i).val, Finset.sum_pos (fun i _ => (a i).property) hne⟩
def posProd {m : ℕ} (a : Fin m → PosNat) (S : Finset (Fin m)) : PosNat :=
  ⟨∏ i ∈ S, (a i).val, Finset.prod_pos (fun i _ => (a i).property)⟩
def PaperPositiveConjecture : Prop :=
  ∀ (r m : ℕ), 0 < r → 0 < m → ∀ (χ : PosNat → Fin r) (R D : ℝ),
    2 ≤ R → 1 ≤ D →
    ∃ a : Fin m → PosNat, StrictMono a ∧
      (∀ i, R * ((∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), ((a j).val : ℝ)) +
        (∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), ((a j).val : ℝ))) ^ D < ((a i).val : ℝ)) ∧
      ∃ c : Fin r, ∀ (S : Finset (Fin m)) (hne : S.Nonempty),
        χ (posSum a S hne) = c ∧ χ (posProd a S) = c

theorem strong_to_positive_domain (h : StrongConjecture) : PaperPositiveConjecture := by
  intro r m _hr _hm χ R D hR hD
  let χ' : ℕ → Fin r := fun k => if hk : 0 < k then χ ⟨k, hk⟩ else χ ⟨1, by decide⟩
  obtain ⟨a, hs, hp, hg, c, hc⟩ := h r χ' m R D hR hD
  let ap : Fin m → PosNat := fun i => ⟨a i, hp i⟩
  refine ⟨ap, hs, hg, c, ?_⟩
  intro S hne
  have hsum : 0 < ∑ i ∈ S, a i := Finset.sum_pos (fun i _ => hp i) hne
  have hprod : 0 < ∏ i ∈ S, a i := Finset.prod_pos (fun i _ => hp i)
  simpa [χ', ap, posSum, posProd, hsum, hprod] using hc S hne

theorem positive_domain_to_strong (h : PaperPositiveConjecture) : StrongConjecture := by
  intro r χ m R D hR hD
  have hr : 0 < r := by have hh := (χ 0).isLt; omega
  by_cases hm : m = 0
  · subst m
    refine ⟨Fin.elim0, ?_, ?_, ?_, χ 0, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro S hne
      obtain ⟨i, _⟩ := hne
      exact Fin.elim0 i
  · obtain ⟨a, hs, hg, c, hc⟩ := h r m hr (Nat.pos_of_ne_zero hm) (fun k => χ k.val) R D hR hD
    refine ⟨fun i => (a i).val, hs, fun i => (a i).property, hg, c, ?_⟩
    intro S hne
    exact hc S hne

theorem strong_iff_paper_positive : StrongConjecture ↔ PaperPositiveConjecture :=
  ⟨strong_to_positive_domain, positive_domain_to_strong⟩
#print axioms strong_iff_paper_positive
