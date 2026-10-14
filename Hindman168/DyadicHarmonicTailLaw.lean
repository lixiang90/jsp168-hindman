import Hindman168.DyadicHarmonicConditioning

/-! The original independent tail law after exposing dyadic finite sets.
Its product coefficient bound is `2^|T|`, with no additional independence
assumption. The tail product lies in the corresponding dyadic product range. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

noncomputable def dyadicHarmonicTailMass {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) : Mass (ι → ℕ) :=
  piMass (fun i => conditionMass (rawMass (X i) W) (fun p => p ∈ S i))

theorem dyadicHarmonicTailMass_eq_condition {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) :
    dyadicHarmonicTailMass X W S =
      conditionMass (piMass (fun i => rawMass (X i) W)) (fun x => ∀ i, x i ∈ S i) := by
  rw [dyadicHarmonicTailMass, piMass_conditionMass, conditionMass, event_piMass_all]
  rfl

theorem dyadicHarmonicTailMass_nonneg {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ)
    (hZ : ∀ i, 0 < harmonicNormalizer (X i) W) (x : ι → ℕ) :
    0 ≤ dyadicHarmonicTailMass X W S x :=
  piMass_nonneg _ (fun i => conditionMass_nonneg _ _
    (fun p => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hZ i) p)) x

theorem dyadicHarmonicTailMass_support {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) {x : ι → ℕ}
    (hx : x ∈ (dyadicHarmonicTailMass X W S).support) (i : ι) : x i ∈ S i := by
  have hi := Fintype.mem_piFinset.mp (piMass_support _ hx) i
  by_contra hn
  apply Finsupp.mem_support_iff.mp hi
  rw [conditionMass_apply, if_neg hn]

theorem dyadicHarmonicTailMass_total {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (S i).Nonempty) (hS : ∀ i, S i ⊆ harmonicWindow (X i) W)
    (hdy : ∀ i p, p ∈ S i → A i ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A i) :
    total (dyadicHarmonicTailMass X W S) = 1 :=
  piMass_total_one _ (fun i => conditionMass_total _ _
    (dyadic_rawMass_event_pos (hA i) (hZ i) (hne i) (hS i) (hdy i)))

theorem dyadicHarmonicTailMass_uniform_bound {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (S i).Nonempty) (hS : ∀ i, S i ⊆ harmonicWindow (X i) W)
    (hdy : ∀ i p, p ∈ S i → A i ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A i) (x : ι → ℕ) :
    dyadicHarmonicTailMass X W S x ≤
      2 ^ Fintype.card ι * piMass (fun i => uniformFinsetMass (S i)) x := by
  have hh := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => conditionMass_nonneg (rawMass (X i) W) (fun p => p ∈ S i)
      (fun p => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hZ i) p) (x i))
    (fun i _ => dyadic_harmonic_uniform_bound (hA i) (hZ i) (hne i) (hS i) (hdy i) (x i))
  simpa only [dyadicHarmonicTailMass, piMass_apply, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ] using hh

theorem dyadicHarmonicTailMass_event_uniform_bound {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (S i).Nonempty) (hS : ∀ i, S i ⊆ harmonicWindow (X i) W)
    (hdy : ∀ i p, p ∈ S i → A i ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A i)
    (B : (ι → ℕ) → Prop) :
    event (dyadicHarmonicTailMass X W S) B ≤
      2 ^ Fintype.card ι * event (piMass (fun i => uniformFinsetMass (S i))) B :=
  event_pointwise_domination _ _
    (dyadicHarmonicTailMass_uniform_bound X W S A hA hZ hne hS hdy) B

theorem dyadicHarmonicTailMass_product_bounds {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i)
    (hdy : ∀ i p, p ∈ S i → A i ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A i)
    {x : ι → ℕ} (hx : x ∈ (dyadicHarmonicTailMass X W S).support) :
    (∏ i, A i) ≤ (∏ i, (x i : ℝ)) ∧
      (∏ i, (x i : ℝ)) ≤ 2 ^ Fintype.card ι * ∏ i, A i := by
  have hd (i : ι) := hdy i (x i) (dyadicHarmonicTailMass_support X W S hx i)
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hA i).le) (fun i _ => (hd i).1)
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => Nat.cast_nonneg (x i)) (fun i _ => (hd i).2)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using hh

end Hindman168
