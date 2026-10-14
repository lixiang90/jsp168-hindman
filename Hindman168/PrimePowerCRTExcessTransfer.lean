import Hindman168.PrimePowerUnitExcess
import Hindman168.FiniteExcessTransfer
import Hindman168.FiniteWeightedErrors

/-!
# Prime-parameter error at the original divisor-dependent CRT modulus

The original prime law is pushed to the actual CRT parameter residues.
The restricted alpha excess is first dominated by beta under that law.
Only this bounded beta test is transferred to the original uniform-unit
law; the event is dropped, without normalizing its probability.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primePowerCRTBadEvent {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : ι → ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ZMod (∏ i, p i ^ e i)) (i : ι) : Prop :=
  primePowerUnitTest (p i) (e i) D
    (fun j => ZMod.prodEquivPi (fun i => p i ^ e i)
      (primePowerModuli_pairwise_coprime p hp hinj e) (x j) i)

theorem primePowerLocalAlpha_excess_le_beta_active (p q d A e : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A) (he : ∀ u, a u ≤ e)
    (c : Fin q → Fin d → ℤ) (bad : Prop)
    (hprimitive : ∀ u, ∃ j, (c u j : ZMod p) ≠ 0)
    (hindependent : e ≠ 0 → ¬ bad → ∀ u v, u ≠ v → LinearIndependent (ZMod p)
      ![(fun j => (c u j : ZMod p)), (fun j => (c v j : ZMod p))]) :
    0 ≤ primePowerLocalAlpha p q d A a ha c - 1 ∧
      primePowerLocalAlpha p q d A a ha c - 1 ≤ localExcessBeta p a bad := by
  by_cases hz : e = 0
  · have ha0 : ∀ u, a u = 0 := fun u => by have h := he u; omega
    rw [primePowerLocalAlpha_all_zero p q d A a ha c ha0,
      localExcessBeta_zero_of_all_zero p a ha0 bad]
    norm_num
  · exact primePowerLocalAlpha_excess_le_beta p q d A hp a ha c bad hprimitive (hindependent hz)

theorem primePowerCRT_beta_expectation_transfer {ι α : Type*} [Fintype ι] {q n : ℕ}
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : ι → ℕ) [NeZero (∏ i, p i ^ e i)]
    (a : ι → Fin q → ℕ) (D : Finset (MvPolynomial (Fin n) ℤ))
    (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V)
    (μ : Mass α) (stat : α → Fin n → ZMod (∏ i, p i ^ e i)) :
    |expectation μ (fun x => localExcessBetaProduct p a
        (fun i y => primePowerCRTBadEvent p hp hinj e D y i) (stat x)) -
      primePowerCRTExcessIntegrand p hp hinj e a D| ≤
      ((V ^ q : ℕ) : ℝ) * distance (μ.mapDomain stat)
        (piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, p i ^ e i))) := by
  have h := localExcessBetaProduct_expectation_transfer p a
    (fun i y => primePowerCRTBadEvent p hp hinj e D y i) V hV
    (μ.mapDomain stat) (piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, p i ^ e i)))
  rw [expectation_push] at h
  exact h

theorem restricted_primePower_alpha_crt_transfer {ι α : Type*} [Fintype ι] {q d n : ℕ}
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : ι → ℕ) [NeZero (∏ i, p i ^ e i)]
    (a : ι → Fin q → ℕ) (ha : ∀ i u, a i u ≤ e i) (D : Finset (MvPolynomial (Fin n) ℤ))
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (stat : α → Fin n → ZMod (∏ i, p i ^ e i)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (hprimitive : ∀ x, E x → ∀ i u, ∃ j, (c x u j : ZMod (p i)) ≠ 0)
    (hindependent : ∀ x, E x → ∀ i, e i ≠ 0 →
      ¬ primePowerCRTBadEvent p hp hinj e D (stat x) i →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p i))
          ![(fun j => (c x u j : ZMod (p i))), (fun j => (c x v j : ZMod (p i)))])
    (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V) :
    0 ≤ expectation μ (fun x => if E x then
      (∏ i, primePowerLocalAlpha (p i) q d (rowMaxValuation (a i)) (a i)
        (rowValuation_le_max (a i)) (c x)) - 1 else 0) ∧
    expectation μ (fun x => if E x then
      (∏ i, primePowerLocalAlpha (p i) q d (rowMaxValuation (a i)) (a i)
        (rowValuation_le_max (a i)) (c x)) - 1 else 0) ≤
      primePowerCRTExcessIntegrand p hp hinj e a D + ((V ^ q : ℕ) : ℝ) *
        distance (μ.mapDomain stat) (piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, p i ^ e i))) := by
  let f := fun x => if E x then
    (∏ i, primePowerLocalAlpha (p i) q d (rowMaxValuation (a i)) (a i)
      (rowValuation_le_max (a i)) (c x)) - 1 else 0
  let g := fun x => localExcessBetaProduct p a
    (fun i y => primePowerCRTBadEvent p hp hinj e D y i) (stat x)
  have hpoint (x : α) : 0 ≤ f x ∧ f x ≤ g x := by
    apply prod_excess_indicator_domination
    · intro i
      exact (primePowerLocalAlpha_bounds (p i) q d _ (a i) (rowValuation_le_max (a i)) (c x)).1
    · intro i
      exact localExcessBeta_nonneg (p i) (a i) _
    · intro hx i
      exact (primePowerLocalAlpha_excess_le_beta_active (p i) q d _ (e i) (hp i)
        (a i) (rowValuation_le_max (a i)) (ha i) (c x)
        (primePowerCRTBadEvent p hp hinj e D (stat x) i) (hprimitive x hx i)
        (hindependent x hx i)).2
  have h0 := expectation_nonneg μ f hμ (fun x => (hpoint x).1)
  have hdom := expectation_mono μ f g hμ (fun x => (hpoint x).2)
  have htrans := primePowerCRT_beta_expectation_transfer p hp hinj e a D V hV μ stat
  have hle := (le_abs_self (expectation μ g - primePowerCRTExcessIntegrand p hp hinj e a D)).trans htrans
  exact ⟨h0, by linarith⟩

end Hindman168
