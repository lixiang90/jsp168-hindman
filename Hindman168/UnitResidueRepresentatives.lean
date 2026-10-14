import Hindman168.PolynomialUnitQuotients
import Hindman168.PrimeResidueLaw

/-!
# Natural representatives of actual uniform unit laws

The natural primitive-residue law already used by the prime stages is
exactly the pushforward of the finite unit law by ZMod.val. Polynomial
divisibility for these representatives therefore has the same probability
as the corresponding reduced polynomial-family event at every divisor.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem zmodUnitUniformMass_val (q : ℕ) [NeZero q] :
    (zmodUnitUniformMass q).mapDomain ZMod.val = primeUnitUniformMass q := by
  ext a
  by_cases ha : a < q
  · have hv : (a : ZMod q).val = a := ZMod.val_natCast_of_lt ha
    rw [← hv, Finsupp.mapDomain_apply (ZMod.val_injective q), zmodUnitUniformMass_apply]
    rw [primeUnitUniformMass, flatMass_apply]
    simp only [primeUnitResidues_mem, ZMod.val_lt, true_and, one_div]
    have hu : IsUnit (a : ZMod q) ↔ (a : ZMod q).val.Coprime q := by
      rw [hv, ZMod.isUnit_iff_coprime]
    simp only [hu]
  · have hz : ((zmodUnitUniformMass q).mapDomain ZMod.val) a = 0 := by
      apply Finsupp.mapDomain_of_not_mem_image_support
      rintro ⟨r, _, hr⟩
      exact ha (hr ▸ ZMod.val_lt r)
    rw [hz, primeUnitUniformMass, flatMass_apply]
    simp only [primeUnitResidues_mem, ha, false_and, if_false]

theorem primeUnitUniformMass_cast (q : ℕ) [NeZero q] :
    (primeUnitUniformMass q).mapDomain (fun a : ℕ => (a : ZMod q)) = zmodUnitUniformMass q := by
  rw [← zmodUnitUniformMass_val, ← Finsupp.mapDomain_comp]
  have hf : (fun a : ℕ => (a : ZMod q)) ∘ ZMod.val = id := by
    funext r
    exact ZMod.natCast_zmod_val r
  rw [hf, Finsupp.mapDomain_id]

theorem primeUnitUniformPi_quotient {Q q : ℕ} [NeZero Q] [NeZero q]
    (h : q ∣ Q) (n : ℕ) :
    (piMass (fun _ : Fin n => primeUnitUniformMass Q)).mapDomain
      (fun x i => (x i : ZMod q)) = piMass (fun _ : Fin n => zmodUnitUniformMass q) := by
  rw [piMass_map]
  have hm : (primeUnitUniformMass Q).mapDomain (fun a : ℕ => (a : ZMod q)) =
      zmodUnitUniformMass q := by
    have hf : (fun a : ℕ => (a : ZMod q)) =
        (ZMod.castHom h (ZMod q)) ∘ (fun a : ℕ => (a : ZMod Q)) := by
      funext a
      simp
    rw [hf, Finsupp.mapDomain_comp, primeUnitUniformMass_cast, zmodUnitUniformMass_quotient h]
  simp only [hm]

def integerPolynomialDivisibilityEvent {n : ℕ} (q : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) : Prop :=
  ∃ f ∈ D, (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) f

theorem integerPolynomial_natCast_eval {n : ℕ} (q : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) :
    (MvPolynomial.eval (fun i => (x i : ℤ)) f : ZMod q) =
      MvPolynomial.eval (fun i => (x i : ZMod q))
        (MvPolynomial.map (Int.castRingHom (ZMod q)) f) := by
  change (Int.castRingHom (ZMod q)) (MvPolynomial.eval (fun i => (x i : ℤ)) f) = _
  rw [← MvPolynomial.eval₂_id (g := fun i => (x i : ℤ)) f,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id,
    MvPolynomial.eval₂_eq_eval_map]
  simp [Function.comp_def]

theorem integerPolynomialDivisibilityEvent_iff {n : ℕ} (q : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) :
    integerPolynomialDivisibilityEvent q D x ↔
      ∃ f ∈ D, finitePolynomialZeroEvent q f (fun i => (x i : ZMod q)) := by
  simp only [integerPolynomialDivisibilityEvent, finitePolynomialZeroEvent,
    ← integerPolynomial_natCast_eval, CharP.intCast_eq_zero_iff (ZMod q) q]

theorem primeUnitUniform_polynomial_divisor_probability {Q q : ℕ}
    [NeZero Q] [NeZero q] (h : q ∣ Q) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    event (piMass (fun _ : Fin n => primeUnitUniformMass Q))
      (integerPolynomialDivisibilityEvent q D) = finitePolynomialUnitFamilyProbability q D := by
  have he : integerPolynomialDivisibilityEvent q D =
      (fun x => ∃ f ∈ D, finitePolynomialZeroEvent q f (fun i => (x i : ZMod q))) := by
    funext x
    exact propext (integerPolynomialDivisibilityEvent_iff q D x)
  rw [he]
  have hm := event_map (piMass (fun _ : Fin n => primeUnitUniformMass Q))
    (fun (x : Fin n → ℕ) i => (x i : ZMod q))
    (fun x => ∃ f ∈ D, finitePolynomialZeroEvent q f x)
  rw [primeUnitUniformPi_quotient h n] at hm
  exact hm.symm

end Hindman168
