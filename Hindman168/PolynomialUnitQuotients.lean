import Hindman168.FinitePolynomialUnitEvents

/-!
# Polynomial events under exact uniform unit quotient laws

Coordinate reduction of an independent uniform unit tuple preserves the
uniform unit product law. Integer polynomial evaluation commutes with
this reduction. Thus polynomial-family exceptions at a divisor modulus
have exactly their small-modulus probability under the large-modulus law.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem zmodUnitUniformPi_quotient {Q q : ℕ} [NeZero Q] [NeZero q]
    (h : q ∣ Q) (n : ℕ) :
    (piMass (fun _ : Fin n => zmodUnitUniformMass Q)).mapDomain
      (fun x i => ZMod.castHom h (ZMod q) (x i)) =
      piMass (fun _ : Fin n => zmodUnitUniformMass q) := by
  rw [piMass_map]
  simp only [zmodUnitUniformMass_quotient h]

theorem integerPolynomial_quotient_eval {Q q : ℕ} (h : q ∣ Q) {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ZMod Q) :
    ZMod.castHom h (ZMod q)
      (MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod Q)) f)) =
    MvPolynomial.eval (fun i => ZMod.castHom h (ZMod q) (x i))
      (MvPolynomial.map (Int.castRingHom (ZMod q)) f) := by
  have hc : (ZMod.castHom h (ZMod q)).comp (Int.castRingHom (ZMod Q)) =
      Int.castRingHom (ZMod q) := by ext z; simp
  simp only [← MvPolynomial.eval₂_eq_eval_map, MvPolynomial.eval₂_comp_left, hc]
  rfl

theorem zmodUnitUniform_quotient_event {Q q : ℕ} [NeZero Q] [NeZero q]
    (h : q ∣ Q) (n : ℕ) (E : (Fin n → ZMod q) → Prop) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass Q))
      (fun x => E (fun i => ZMod.castHom h (ZMod q) (x i))) =
    event (piMass (fun _ : Fin n => zmodUnitUniformMass q)) E := by
  rw [← event_map, zmodUnitUniformPi_quotient h n]

theorem finitePolynomialUnitFamilyProbability_quotient {Q q : ℕ}
    [NeZero Q] [NeZero q] (h : q ∣ Q) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass Q))
      (fun x => ∃ f ∈ D, ZMod.castHom h (ZMod q)
        (MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod Q)) f)) = 0) =
    finitePolynomialUnitFamilyProbability q D := by
  simp only [integerPolynomial_quotient_eval]
  exact zmodUnitUniform_quotient_event h n (fun x => ∃ f ∈ D, finitePolynomialZeroEvent q f x)

end Hindman168
