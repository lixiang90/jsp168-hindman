import Hindman168.EventMass
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic.Linarith

/-!
# Schwartz--Zippel for arbitrary independent finite probability laws

For each coordinate, the atom bound is its actual maximum probability,
not the reciprocal cardinality of its support. The induction follows
mathlib's first-variable / leading-coefficient decomposition, but sums
the original weights throughout.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem polynomial_zero_event_le {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p ≠ 0) (μ : Mass R) {b : ℝ}
    (hb : 0 ≤ b) (hcap : ∀ x, μ x ≤ b) :
    event μ (fun x => p.eval x = 0) ≤ (p.natDegree : ℝ) * b := by
  rw [event_eq_filter]
  have hsub : μ.support.filter (fun x => p.eval x = 0) ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hx).2)
  have hc := (Finset.card_le_card hsub).trans
    (p.roots.toFinset_card_le.trans p.card_roots')
  calc
    _ ≤ ∑ x ∈ μ.support.filter (fun x => p.eval x = 0), b :=
      Finset.sum_le_sum (fun x _ => hcap x)
    _ = (μ.support.filter (fun x => p.eval x = 0)).card * b := by simp
    _ ≤ (p.natDegree : ℝ) * b :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hb

/-- A degree-weighted atom bound for genuinely nonuniform independent
coordinates. The polynomial is required to be nonzero over the domain. -/
theorem weighted_schwartz_zippel {R : Type*} [CommRing R] [IsDomain R] :
    ∀ {n : ℕ} {p : MvPolynomial (Fin n) R}, p ≠ 0 →
      ∀ (μ : Fin n → Mass R), (∀ i x, 0 ≤ μ i x) → (∀ i, total (μ i) = 1) →
      ∀ (b : Fin n → ℝ), (∀ i, 0 ≤ b i) → (∀ i x, μ i x ≤ b i) →
        event (piMass μ) (fun x => MvPolynomial.eval x p = 0) ≤
          ∑ i, (p.degreeOf i : ℝ) * b i
  | 0, p, hp, μ, _hμ, _ht, b, _hb, _hcap => by
    rw [p.eq_C_of_isEmpty] at hp ⊢
    have hpC := MvPolynomial.C_ne_zero.mp hp
    simp [event, Finsupp.sum, MvPolynomial.eval_C, hpC]
  | n + 1, p, hp, μ, hμ, ht, b, hb, hcap => by
    let p' := MvPolynomial.finSuccEquiv R n p
    let q := p'.leadingCoeff
    have hp' : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hp
    have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
    let ν := piMass (fun i : Fin n => μ i.succ)
    have hν : ∀ x, 0 ≤ ν x := piMass_nonneg _ (fun i => hμ i.succ)
    have htν : total ν = 1 := piMass_total_one _ (fun i => ht i.succ)
    have hfiber (x : Fin n → R) :
        event (μ 0) (fun a => MvPolynomial.eval (Fin.cons a x) p = 0) ≤
          (if MvPolynomial.eval x q = 0 then 1 else 0) + (p.degreeOf 0 : ℝ) * b 0 := by
      by_cases hx : MvPolynomial.eval x q = 0
      · rw [if_pos hx]
        have hle := event_le_total (μ 0)
          (fun a => MvPolynomial.eval (Fin.cons a x) p = 0) (hμ 0)
        rw [ht 0] at hle
        exact hle.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hb 0)))
      · rw [if_neg hx, zero_add]
        let r := p'.map (MvPolynomial.eval x)
        have hr : r ≠ 0 := by
          intro hz
          have hc := congrArg (fun f : Polynomial R => f.coeff p'.natDegree) hz
          simp only [r, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
          exact hx (by simpa only [q, Polynomial.leadingCoeff] using hc)
        simp_rw [MvPolynomial.eval_eq_eval_mv_eval']
        have he := polynomial_zero_event_le r hr (μ 0) (hb 0) (hcap 0)
        have hdeg : r.natDegree ≤ p.degreeOf 0 := by
          exact Polynomial.natDegree_map_le.trans_eq (MvPolynomial.natDegree_finSuccEquiv p)
        exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (hb 0))
    rw [event_piMass_cons]
    calc
      _ ≤ ∑ x ∈ ν.support, ν x *
          ((if MvPolynomial.eval x q = 0 then 1 else 0) + (p.degreeOf 0 : ℝ) * b 0) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfiber x) (hν x))
      _ = event ν (fun x => MvPolynomial.eval x q = 0) + (p.degreeOf 0 : ℝ) * b 0 := by
        rw [event_eq_sum ν _ (Finset.Subset.refl _)]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        have he : (∑ x ∈ ν.support, ν x * (if MvPolynomial.eval x q = 0 then 1 else 0)) =
            ∑ x ∈ ν.support, if MvPolynomial.eval x q = 0 then ν x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> simp
        rw [he, ← total_eq_sum ν (Finset.Subset.refl _), htν, one_mul]
      _ ≤ (∑ i : Fin n, (q.degreeOf i : ℝ) * b i.succ) + (p.degreeOf 0 : ℝ) * b 0 :=
        add_le_add (weighted_schwartz_zippel hq _ (fun i => hμ i.succ)
          (fun i => ht i.succ) (fun i => b i.succ) (fun i => hb i.succ) (fun i => hcap i.succ)) le_rfl
      _ ≤ (∑ i : Fin n, (p.degreeOf i.succ : ℝ) * b i.succ) + (p.degreeOf 0 : ℝ) * b 0 := by
        apply add_le_add _ le_rfl
        apply Finset.sum_le_sum
        intro i _
        have hdeg : q.degreeOf i ≤ p.degreeOf i.succ :=
          MvPolynomial.degreeOf_coeff_finSuccEquiv p i p'.natDegree
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (hb i.succ)
      _ = ∑ i, (p.degreeOf i : ℝ) * b i := by rw [Fin.sum_univ_succ, add_comm]

theorem weighted_schwartz_zippel_uniform_cap {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (μ : Fin n → Mass R) (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i) = 1)
    {b : ℝ} (hb : 0 ≤ b) (hcap : ∀ i x, μ i x ≤ b) :
    event (piMass μ) (fun x => MvPolynomial.eval x p = 0) ≤
      (∑ i, (p.degreeOf i : ℝ)) * b := by
  simpa only [← Finset.sum_mul] using
    weighted_schwartz_zippel hp μ hμ ht (fun _ => b) (fun _ => hb) hcap

theorem mass_map_injective_atom_bound {α β : Type*} (μ : Mass α) (f : α → β)
    (hf : Function.Injective f) {b : ℝ} (hb : 0 ≤ b) (hcap : ∀ x, μ x ≤ b) (y : β) :
    μ.mapDomain f y ≤ b := by
  by_cases hy : μ.mapDomain f y = 0
  · simpa only [hy] using hb
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp
      (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hy))
    rw [Finsupp.mapDomain_apply hf μ x]
    exact hcap x

/-- Injectively encoding sampled values into the polynomial's domain does
not turn the weighted law into a uniform law. -/
theorem weighted_schwartz_zippel_injective {α R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (μ : Fin n → Mass α) (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i) = 1)
    (f : α → R) (hf : Function.Injective f) {b : ℝ}
    (hb : 0 ≤ b) (hcap : ∀ i x, μ i x ≤ b) :
    event (piMass μ) (fun x => MvPolynomial.eval (fun i => f (x i)) p = 0) ≤
      (∑ i, (p.degreeOf i : ℝ)) * b := by
  have he := weighted_schwartz_zippel_uniform_cap hp
    (fun i => (μ i).mapDomain f) (fun i => push_nonneg (μ i) f (hμ i))
    (fun i => by rw [total_push, ht i]) hb
    (fun i => mass_map_injective_atom_bound (μ i) f hf hb (hcap i))
  rw [← piMass_map, event_map] at he
  exact he

theorem weighted_polynomial_family_zero_bound {α R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (D : Finset (MvPolynomial (Fin n) R)) (hD : ∀ p ∈ D, p ≠ 0)
    (μ : Fin n → Mass α) (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i) = 1)
    (f : α → R) (hf : Function.Injective f) {b : ℝ}
    (hb : 0 ≤ b) (hcap : ∀ i x, μ i x ≤ b) :
    event (piMass μ) (fun x => ∃ p ∈ D, MvPolynomial.eval (fun i => f (x i)) p = 0) ≤
      (∑ p ∈ D, ∑ i, (p.degreeOf i : ℝ)) * b := by
  calc
    _ ≤ ∑ p ∈ D, event (piMass μ)
        (fun x => MvPolynomial.eval (fun i => f (x i)) p = 0) :=
      event_union_bound _ D _ (piMass_nonneg μ hμ)
    _ ≤ ∑ p ∈ D, (∑ i, (p.degreeOf i : ℝ)) * b :=
      Finset.sum_le_sum (fun p hp =>
        weighted_schwartz_zippel_injective (hD p hp) μ hμ ht f hf hb hcap)
    _ = _ := (Finset.sum_mul _ _ _).symm

end Hindman168
