import Hindman168.PrimePolynomialEvents

/-!
# Good prime samples have probability tending to one

Polynomial nonvanishing and pairwise distinctness are combined into one
event under the original independent law. Positive event mass yields an
actual supported tuple; the probability estimates do not select a tuple
outside the pool.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_or_le {α : Type*} (μ : Mass α) (E F : α → Prop) (hμ : ∀ x, 0 ≤ μ x) :
    event μ (fun x => E x ∨ F x) ≤ event μ E + event μ F := by
  rw [event_eq_sum μ _ (Finset.Subset.refl _), event_eq_sum μ E (Finset.Subset.refl _),
    event_eq_sum μ F (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, hμ x]

theorem event_complement {α : Type*} (μ : Mass α) (E : α → Prop) :
    event μ (fun x => ¬ E x) = total μ - event μ E := by
  rw [event_eq_sum μ _ (Finset.Subset.refl _), total_eq_sum μ (Finset.Subset.refl _),
    event_eq_sum μ E (Finset.Subset.refl _), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x <;> simp [he]

theorem exists_supported_of_event_pos {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (he : 0 < event μ E) : ∃ x ∈ μ.support, E x := by
  rw [event_eq_filter] at he
  obtain ⟨x, hx, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hμ x)).mp he
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

def primeSampleGood {n : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) : Prop :=
  Function.Injective x ∧ ∀ p ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) p ≠ 0

noncomputable def primeBadSampleMass {n : ℕ} (A B : ℕ) (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  event (primeIndependentMass n A B) (fun x =>
    (∃ p ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) p = 0) ∨ (∃ i j, i ≠ j ∧ x i = x j))

noncomputable def primeGoodSampleMass {n : ℕ} (A B : ℕ) (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  event (primeIndependentMass n A B) (primeSampleGood D)

theorem primeSampleGood_iff_not_bad {n : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) :
    primeSampleGood D x ↔ ¬ ((∃ p ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) p = 0) ∨
      (∃ i j, i ≠ j ∧ x i = x j)) := by
  unfold primeSampleGood Function.Injective
  constructor
  · rintro ⟨hinj, hD⟩ (⟨p, hp, hz⟩ | ⟨i, j, hij, heq⟩)
    · exact hD p hp hz
    · exact hij (hinj heq)
  · intro h
    constructor
    · intro i j heq
      by_contra hij
      exact h (Or.inr ⟨i, j, hij, heq⟩)
    · intro p hp hz
      exact h (Or.inl ⟨p, hp, hz⟩)

theorem primeGoodSampleMass_eq_one_sub {n A B : ℕ}
    (hH : 0 < primePoolHarmonicMass A B) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    primeGoodSampleMass A B D = 1 - primeBadSampleMass A B D := by
  unfold primeGoodSampleMass primeBadSampleMass
  have heq : primeSampleGood D = (fun x => ¬ ((∃ p ∈ D,
      MvPolynomial.eval (fun i => (x i : ℤ)) p = 0) ∨ (∃ i j, i ≠ j ∧ x i = x j))) := by
    funext x
    exact propext (primeSampleGood_iff_not_bad D x)
  rw [heq]
  rw [event_complement, primeIndependentMass_total hH]

theorem primeBadSampleMass_bound {n A B : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A B) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    primeBadSampleMass A B D ≤ ((∑ p ∈ D, ∑ i, (p.degreeOf i : ℝ)) + 2 * (n : ℝ) ^ 2) *
      (1 / ((A : ℝ) * primePoolHarmonicMass A B)) := by
  have he := event_or_le (primeIndependentMass n A B)
    (fun x => ∃ p ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) p = 0)
    (fun x => ∃ i j, i ≠ j ∧ x i = x j) (primeIndependentMass_nonneg n A B)
  exact he.trans ((add_le_add (primePolynomialFamilyZeroMass_bound hA hH D hD)
    (primeRepeatedMass_bound hA hH)).trans_eq (add_mul _ _ _).symm)

theorem primeIndependentMass_support_pool {n A B : ℕ} {x : Fin n → ℕ}
    (hx : x ∈ (primeIndependentMass n A B).support) : ∀ i, x i ∈ primePool A B := by
  classical
  have hx' := piMass_support (fun _ : Fin n => primePoolMass A B) hx
  intro i
  apply primePoolMass_support A B
  exact (@Fintype.mem_piFinset (Fin n) (Classical.decEq _) inferInstance
    (fun _ => ℕ) _ x).mp hx' i

theorem growingPrimeBadSampleMass_rapid {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      primeBadSampleMass (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D) := by
  apply ((equidistributedGrowingPrimePool_atom_cap_rapid hQ hV).const_mul
    ((∑ p ∈ D, ∑ i, (p.degreeOf i : ℝ)) + 2 * (n : ℝ) ^ 2)).of_abs_le
  apply Eventually.of_forall
  intro w
  have hn : 0 ≤ primeBadSampleMass
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D :=
    event_nonneg _ _ (primeIndependentMass_nonneg _ _ _)
  rw [abs_of_nonneg hn]
  exact (primeBadSampleMass_bound (Nat.pow_pos (by decide : 0 < 2))
    (equidistributedGrowingPrimePool_mass_pos (V w) (Q w) w (hQ w)) D hD).trans (le_abs_self _)

theorem growingPrimeGoodSampleMass_tendsto_one {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0) :
    Tendsto (fun w => primeGoodSampleMass
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D) atTop (𝓝 1) := by
  have hz : Tendsto (fun w => primeBadSampleMass
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D) atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using (growingPrimeBadSampleMass_rapid hQ hV D hD) 0
  have he := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hz
  simpa only [primeGoodSampleMass_eq_one_sub
    (equidistributedGrowingPrimePool_mass_pos _ _ _ _), sub_zero] using he

theorem growingPrimePool_exists_good_eventually {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0) :
    ∀ᶠ w in atTop, ∃ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper) ∧ primeSampleGood D x := by
  have hp := (growingPrimeGoodSampleMass_tendsto_one hQ hV D hD).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hp] with w hw
  obtain ⟨x, hx, hg⟩ := exists_supported_of_event_pos _ (primeSampleGood D)
    (primeIndependentMass_nonneg _ _ _) hw
  exact ⟨x, primeIndependentMass_support_pool hx, hg⟩

end Hindman168
