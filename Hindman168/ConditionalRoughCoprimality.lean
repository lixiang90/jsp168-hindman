import Hindman168.PrimePoolRoughCoprimality

/-!
# Rough-coprimality bounds after actual tuple-event conditioning

The conditional law is the restricted original finite mass divided by its
actual event mass. The two tuples are conditioned separately, preserving
their independence. Events of probability tending to one eventually have
mass at least one half, so a uniform factor four preserves the proved
zero and rough-gcd error orders.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def conditionMass {α : Type*} (μ : Mass α) (E : α → Prop) : Mass α := by
  classical
  exact (event μ E)⁻¹ • μ.filter E

theorem conditionMass_apply {α : Type*} (μ : Mass α) (E : α → Prop) (x : α) :
    conditionMass μ E x = if E x then μ x / event μ E else 0 := by
  classical
  simp only [conditionMass, Finsupp.smul_apply, smul_eq_mul, Finsupp.filter_apply]
  by_cases hx : E x <;> simp [hx, div_eq_mul_inv, mul_comm]

theorem conditionMass_support {α : Type*} (μ : Mass α) (E : α → Prop) :
    (conditionMass μ E).support ⊆ μ.support := by
  intro x hx
  apply Finsupp.mem_support_iff.mpr
  intro hzero
  apply Finsupp.mem_support_iff.mp hx
  rw [conditionMass_apply, hzero]
  split_ifs <;> simp

theorem conditionMass_nonneg {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (x : α) : 0 ≤ conditionMass μ E x := by
  rw [conditionMass_apply]
  split_ifs
  · exact div_nonneg (hμ x) (event_nonneg μ E hμ)
  · exact le_rfl

theorem conditionMass_total {α : Type*} (μ : Mass α) (E : α → Prop)
    (hE : 0 < event μ E) : total (conditionMass μ E) = 1 := by
  rw [total_eq_sum _ (conditionMass_support μ E)]
  calc
    (∑ x ∈ μ.support, conditionMass μ E x) =
        (∑ x ∈ μ.support, if E x then μ x else 0) / event μ E := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [conditionMass_apply]
      split_ifs <;> simp
    _ = 1 := by rw [← event_eq_sum μ E (Finset.Subset.refl _), div_self hE.ne']

theorem event_tensor_conditionMass {α β : Type*} (μ : Mass α) (ν : Mass β)
    (A : α → Prop) (C : β → Prop) (B : α × β → Prop) :
    event (tensor (conditionMass μ A) (conditionMass ν C)) B =
      event (tensor μ ν) (fun xy => A xy.1 ∧ C xy.2 ∧ B xy) / (event μ A * event ν C) := by
  classical
  have hS : (tensor (conditionMass μ A) (conditionMass ν C)).support ⊆ μ.support ×ˢ ν.support := by
    intro xy hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (tensor_support _ _ hxy)
    exact Finset.mem_product.mpr ⟨conditionMass_support μ A hx, conditionMass_support ν C hy⟩
  rw [event_eq_sum _ B hS, event_eq_sum _ _ (tensor_support μ ν), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [tensor_apply, conditionMass_apply]
  by_cases hA : A xy.1 <;> by_cases hC : C xy.2 <;> by_cases hB : B xy <;>
    simp [hA, hC, hB, div_mul_div_comm]

theorem event_tensor_conditionMass_le {α β : Type*} (μ : Mass α) (ν : Mass β)
    (A : α → Prop) (C : β → Prop) (B : α × β → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hA : 0 < event μ A) (hC : 0 < event ν C) :
    event (tensor (conditionMass μ A) (conditionMass ν C)) B ≤
      event (tensor μ ν) B / (event μ A * event ν C) := by
  rw [event_tensor_conditionMass]
  exact div_le_div_of_nonneg_right
    (event_mono _ (tensor_nonneg _ _ hμ hν) (fun _ h => h.2.2)) (mul_pos hA hC).le

theorem event_tensor_conditionMass_half_le {α β : Type*} (μ : Mass α) (ν : Mass β)
    (A : α → Prop) (C : β → Prop) (B : α × β → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hA : (1 : ℝ) / 2 ≤ event μ A) (hC : (1 : ℝ) / 2 ≤ event ν C) :
    event (tensor (conditionMass μ A) (conditionMass ν C)) B ≤ 4 * event (tensor μ ν) B := by
  have hApos : 0 < event μ A := by linarith
  have hCpos : 0 < event ν C := by linarith
  have hprod : (1 : ℝ) / 4 ≤ event μ A * event ν C := by
    have h := mul_le_mul hA hC (by norm_num : (0 : ℝ) ≤ 1 / 2) hApos.le
    norm_num at h ⊢
    exact h
  have hB : 0 ≤ event (tensor μ ν) B := event_nonneg _ B (tensor_nonneg _ _ hμ hν)
  calc
    _ ≤ event (tensor μ ν) B / (event μ A * event ν C) :=
      event_tensor_conditionMass_le μ ν A C B hμ hν hApos hCpos
    _ ≤ event (tensor μ ν) B / ((1 : ℝ) / 4) :=
      div_le_div_of_nonneg_left hB (by norm_num) hprod
    _ = _ := by ring

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem exists_conditioned_dyadicPool_rough_coprimality_bounds {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ w0 e0 K : ℕ, ∀ (PF : Fin m → DyadicPrimePool) (PG : Fin n → DyadicPrimePool),
      (∀ i, e0 ≤ (PF i).lowerExponent) → (∀ i, e0 ≤ (PG i).lowerExponent) →
      ∀ (A : (Fin m → ℕ) → Prop) (C : (Fin n → ℕ) → Prop),
      (1 : ℝ) / 2 ≤ event (dyadicPoolTupleMass PF) A →
      (1 : ℝ) / 2 ≤ event (dyadicPoolTupleMass PG) C → ∀ w L : ℕ,
      w0 ≤ w → 0 < w → Real.exp 2 ≤ (L : ℝ) →
      (∀ i, L ≤ (PF i).lower) → (∀ i, L ≤ (PG i).lower) →
      event (tensor (conditionMass (dyadicPoolTupleMass PF) A) (conditionMass (dyadicPoolTupleMass PG) C))
        (polynomialProductZeroEvent F G) ≤ (K : ℝ) * (Real.log (L : ℝ) / L) ∧
      event (tensor (conditionMass (dyadicPoolTupleMass PF) A) (conditionMass (dyadicPoolTupleMass PG) C))
        (roughPolynomialGcdEvent w F G) ≤ (K : ℝ) * dyadicCoprimeError w L := by
  obtain ⟨w0, e0, K, hk⟩ := exists_dyadicPool_rough_coprimality_bounds hF hG
  refine ⟨w0, e0, 4 * K, ?_⟩
  intro PF PG heF heG A C hA hC w L hww hw hL hLF hLG
  have h := hk PF PG heF heG w L hww hw hL hLF hLG
  have hzero := event_tensor_conditionMass_half_le (dyadicPoolTupleMass PF) (dyadicPoolTupleMass PG)
    A C (polynomialProductZeroEvent F G) (dyadicPoolTupleMass_nonneg PF) (dyadicPoolTupleMass_nonneg PG) hA hC
  have hgcd := event_tensor_conditionMass_half_le (dyadicPoolTupleMass PF) (dyadicPoolTupleMass PG)
    A C (roughPolynomialGcdEvent w F G) (dyadicPoolTupleMass_nonneg PF) (dyadicPoolTupleMass_nonneg PG) hA hC
  constructor
  · exact hzero.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left h.1 (by norm_num : (0 : ℝ) ≤ 4))
  · exact hgcd.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left h.2 (by norm_num : (0 : ℝ) ≤ 4))

end Hindman168
