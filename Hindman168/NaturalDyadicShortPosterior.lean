import Hindman168.DyadicShortBinPosterior

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem dyadic_natural_shortBin_uniform_posterior {ι : Type*} [Fintype ι]
    (X : ι → ℕ) (W : ℕ) (S : ι → Finset ℕ) (A : ι → ℕ)
    (hA : ∀ i, 0 < A i) (hZ : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hne : ∀ i, (S i).Nonempty) (hS : ∀ i, S i ⊆ harmonicWindow (X i) W)
    (hdy : ∀ i p, p ∈ S i → A i ≤ p ∧ p ≤ 2 * A i)
    {Q R Xp M r : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (hwidth : (∏ i, A i) * R ≤ Q)
    (hcutlo : Xp * (2 ^ Fintype.card ι * ∏ i, A i) ≤ Q)
    (hcuthi : Q + (∏ i, A i) * R ≤ Xp ^ 2 * ∏ i, A i)
    (hM : 0 < M) (hr : r < M) (hWM : W ∣ M) (hunit : r.Coprime W)
    (hZp : 0 < harmonicNormalizer Xp W)
    (hsmall : 2 * (2 ^ Fintype.card ι : ℝ) * M / R ≤ 1 / 2)
    (B : (ι → ℕ) → Prop) :
    event (conditionMass (conditionalJoint (dyadicHarmonicTailMass X W S)
      (fun _ => rawMass Xp W))
      (fun xp => Q ≤ (∏ i, xp.1 i) * xp.2 ∧
        (∏ i, xp.1 i) * xp.2 < Q + (∏ i, A i) * R ∧ xp.2 % M = r))
      (fun xp => B xp.1) ≤
        (3 * 2 ^ Fintype.card ι) * event (piMass (fun i => uniformFinsetMass (S i))) B := by
  have hp := dyadic_shortBin_uniform_posterior X W S (fun i => (A i : ℝ))
    (fun i => by exact_mod_cast hA i) hZ hne hS
    (fun i p hp => by exact_mod_cast hdy i p hp)
    (Q := (Q : ℝ)) (R := (R : ℝ))
    (by exact_mod_cast hQ) (by exact_mod_cast hR)
    (by exact_mod_cast hwidth) (by exact_mod_cast hcutlo) (by exact_mod_cast hcuthi)
    hM hr hWM hunit hZp hsmall B
  have he : (fun xp : (ι → ℕ) × ℕ => (Q : ℝ) ≤ (∏ i, (xp.1 i : ℝ)) * xp.2 ∧
      (∏ i, (xp.1 i : ℝ)) * xp.2 < Q + (∏ i, (A i : ℝ)) * R ∧ xp.2 % M = r) =
    (fun xp => Q ≤ (∏ i, xp.1 i) * xp.2 ∧
      (∏ i, xp.1 i) * xp.2 < Q + (∏ i, A i) * R ∧ xp.2 % M = r) := by
    funext xp
    apply propext
    norm_cast
  rw [he] at hp
  exact hp

end Hindman168
