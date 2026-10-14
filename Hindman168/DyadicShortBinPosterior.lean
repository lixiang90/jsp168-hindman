import Hindman168.DyadicHarmonicTailLaw

/-! The paper's short-bin posterior is dominated by `3 * 2^|T|` times
the product uniform law on the exposed dyadic residue bins. The actual
tail product is used, and two explicit inequalities ensure full pivot
cutoff containment for every tail tuple. No exact microcell is exposed. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem dyadic_shortBin_uniform_posterior {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (S i).Nonempty) (hS : ∀ i, S i ⊆ harmonicWindow (X i) W)
    (hdy : ∀ i p, p ∈ S i → A i ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A i)
    {Q R : ℝ} {Xp M r : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (hwidth : (∏ i, A i) * R ≤ Q)
    (hcutlo : (Xp : ℝ) * (2 ^ Fintype.card ι * ∏ i, A i) ≤ Q)
    (hcuthi : Q + (∏ i, A i) * R ≤ (Xp ^ 2 : ℕ) * ∏ i, A i)
    (hM : 0 < M) (hr : r < M) (hWM : W ∣ M) (hunit : r.Coprime W)
    (hZp : 0 < harmonicNormalizer Xp W)
    (hsmall : 2 * (2 ^ Fintype.card ι) * M / R ≤ 1 / 2)
    (B : (ι → ℕ) → Prop) :
    event (conditionMass (conditionalJoint (dyadicHarmonicTailMass X W S)
      (fun _ => rawMass Xp W))
      (fun xp => Q ≤ (∏ i, (xp.1 i : ℝ)) * xp.2 ∧
        (∏ i, (xp.1 i : ℝ)) * xp.2 < Q + (∏ i, A i) * R ∧ xp.2 % M = r))
      (fun xp => B xp.1) ≤
        (3 * 2 ^ Fintype.card ι) * event (piMass (fun i => uniformFinsetMass (S i))) B := by
  have ha : 0 < ∏ i, A i := Finset.prod_pos (fun i _ => hA i)
  have ht (x : ι → ℕ) (hx : x ∈ (dyadicHarmonicTailMass X W S).support) :=
    dyadicHarmonicTailMass_product_bounds X W S A hA hdy hx
  have htpos (x : ι → ℕ) (hx : x ∈ (dyadicHarmonicTailMass X W S).support) :
      0 < ∏ i, (x i : ℝ) := ha.trans_le (ht x hx).1
  have hp := shortBin_pivot_posterior_domination (dyadicHarmonicTailMass X W S)
    (fun x => ∏ i, (x i : ℝ)) B
    (dyadicHarmonicTailMass_nonneg X W S hZ)
    (dyadicHarmonicTailMass_total X W S A hA hZ hne hS hdy)
    hQ ha hR hwidth htpos (fun x hx => (ht x hx).2)
    (fun x hx => (le_div_iff₀ (htpos x hx)).mpr
      ((mul_le_mul_of_nonneg_left (ht x hx).2 (Nat.cast_nonneg Xp)).trans hcutlo))
    (fun x hx => (div_le_iff₀ (htpos x hx)).mpr
      (hcuthi.trans (mul_le_mul_of_nonneg_left (ht x hx).1 (Nat.cast_nonneg (Xp ^ 2)))))
    hM hr hWM hunit hZp hsmall
  apply hp.trans
  have hb := mul_le_mul_of_nonneg_left
    (dyadicHarmonicTailMass_event_uniform_bound X W S A hA hZ hne hS hdy B)
    (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [mul_assoc] using hb

theorem dyadic_residue_shortBin_uniform_posterior {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W L : ℕ) (a : ι → ℕ) (A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (residueWindow (A i) (2 * A i) L (a i)).Nonempty)
    (htailLo : ∀ i, (X i : ℝ) ≤ A i) (htailHi : ∀ i, 2 * A i ≤ (X i ^ 2 : ℕ))
    (hWL : W ∣ L) (ha : ∀ i, (a i).Coprime W)
    {Q R : ℝ} {Xp M r : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (hwidth : (∏ i, A i) * R ≤ Q)
    (hcutlo : (Xp : ℝ) * (2 ^ Fintype.card ι * ∏ i, A i) ≤ Q)
    (hcuthi : Q + (∏ i, A i) * R ≤ (Xp ^ 2 : ℕ) * ∏ i, A i)
    (hM : 0 < M) (hr : r < M) (hWM : W ∣ M) (hunit : r.Coprime W)
    (hZp : 0 < harmonicNormalizer Xp W)
    (hsmall : 2 * (2 ^ Fintype.card ι) * M / R ≤ 1 / 2)
    (B : (ι → ℕ) → Prop) :
    event (conditionMass (conditionalJoint
      (dyadicHarmonicTailMass X W (fun i => residueWindow (A i) (2 * A i) L (a i)))
      (fun _ => rawMass Xp W))
      (fun xp => Q ≤ (∏ i, (xp.1 i : ℝ)) * xp.2 ∧
        (∏ i, (xp.1 i : ℝ)) * xp.2 < Q + (∏ i, A i) * R ∧ xp.2 % M = r))
      (fun xp => B xp.1) ≤ (3 * 2 ^ Fintype.card ι) *
        event (piMass (fun i => uniformFinsetMass (residueWindow (A i) (2 * A i) L (a i)))) B :=
  dyadic_shortBin_uniform_posterior X W _ A hA hZ hne
    (fun i => dyadic_residueWindow_subset (htailLo i) (htailHi i) hWL (ha i))
    (fun _ _ hp => ⟨(mem_residueWindow.mp hp).1, (mem_residueWindow.mp hp).2.1.le⟩)
    hQ hR hwidth hcutlo hcuthi hM hr hWM hunit hZp hsmall B

end Hindman168
