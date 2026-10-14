import Hindman168.WeightedSchwartzZippel
import Hindman168.ZModUniformUnits
import Hindman168.IntegerPolynomialValueBounds

/-!
# Actual polynomial bad-test probability on uniform prime units

An integer polynomial remains nonzero modulo every modulus exceeding its
actual coefficient-size sum. Mapping coefficients cannot increase any
coordinate degree. The original uniform unit law has atoms at most 2/p,
so the weighted root bound and a finite union give an explicit C/p bound
for every fixed nonzero integer polynomial family, uniformly in p.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem polynomial_map_degreeOf_le {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (r : R →+* S) (f : MvPolynomial (Fin n) R) (i : Fin n) :
    (MvPolynomial.map r f).degreeOf i ≤ f.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact MvPolynomial.le_degreeOf_of_mem_support i ((MvPolynomial.support_map_subset r f) hd)

theorem integerPolynomial_mod_ne_zero_above_coeffSize {n p : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (hp : integerPolynomialCoeffSize f < p) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hf
  have hc : (f.coeff d).natAbs ≤ integerPolynomialCoeffSize f :=
    Finset.single_le_sum (fun e _ => Nat.zero_le (f.coeff e).natAbs) hd
  have hcp : 0 < (f.coeff d).natAbs := Int.natAbs_pos.mpr (MvPolynomial.mem_support_iff.mp hd)
  intro hz
  have hzero : ((f.coeff d : ℤ) : ZMod p) = 0 := by
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Int.coe_castRingHom] using
      congrArg (MvPolynomial.coeff d) hz
  have hdiv : p ∣ (f.coeff d).natAbs := Int.natCast_dvd.mp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff d) p).mp hzero)
  have := Nat.le_of_dvd hcp hdiv
  omega

theorem zmodUnitUniformMass_prime_atom_le {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    zmodUnitUniformMass p x ≤ 2 / (p : ℝ) := by
  rw [zmodUnitUniformMass_apply]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hφ : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hratio : (p : ℝ) ≤ 2 * (p.totient : ℝ) := by
    exact_mod_cast (show p ≤ 2 * p.totient from by simpa only [pow_one] using prime_power_le_twice_totient hp 1)
  split_ifs
  · rw [← one_div]
    exact (div_le_div_iff₀ hφ hpR).mpr (by simpa only [one_mul] using hratio)
  · positivity

theorem integerPolynomial_prime_unit_zero_bound {n p : ℕ} [NeZero p]
    (hp : p.Prime) (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0)
    (hsize : integerPolynomialCoeffSize f < p) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass p))
      (fun x => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0) ≤
      (∑ i, (f.degreeOf i : ℝ)) * (2 / (p : ℝ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz := weighted_schwartz_zippel_uniform_cap
    (integerPolynomial_mod_ne_zero_above_coeffSize f hf hsize)
    (fun _ : Fin n => zmodUnitUniformMass p) (fun _ => zmodUnitUniformMass_nonneg p)
    (fun _ => zmodUnitUniformMass_total p) (by positivity : (0 : ℝ) ≤ 2 / (p : ℝ))
    (fun _ x => zmodUnitUniformMass_prime_atom_le hp x)
  have hd : (∑ i, ((MvPolynomial.map (Int.castRingHom (ZMod p)) f).degreeOf i : ℝ)) ≤
      ∑ i, (f.degreeOf i : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast polynomial_map_degreeOf_le (Int.castRingHom (ZMod p)) f i
  exact hz.trans (mul_le_mul_of_nonneg_right hd (by positivity))

def unitPolynomialTestEvent {n : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (p : ℕ)
    (x : Fin n → ZMod p) : Prop :=
  ∃ f ∈ D, MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0

theorem integerPolynomial_family_prime_unit_zero_bound {n p : ℕ} [NeZero p]
    (hp : p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hsize : ∀ f ∈ D, integerPolynomialCoeffSize f < p) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p) ≤
      (2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ))) / (p : ℝ) := by
  calc
    _ ≤ ∑ f ∈ D, event (piMass (fun _ : Fin n => zmodUnitUniformMass p))
        (fun x => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0) :=
      event_union_bound _ D _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
    _ ≤ ∑ f ∈ D, (∑ i, (f.degreeOf i : ℝ)) * (2 / (p : ℝ)) :=
      Finset.sum_le_sum (fun f hf => integerPolynomial_prime_unit_zero_bound hp f (hD f hf) (hsize f hf))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem integerPolynomial_family_prime_unit_uniform_bound {n p : ℕ} [NeZero p]
    (hp : p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize < p) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p) ≤
      (2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ))) / (p : ℝ) := by
  apply integerPolynomial_family_prime_unit_zero_bound hp D hD
  intro f hf
  exact (Finset.le_sup (f := integerPolynomialCoeffSize) hf).trans_lt hcut

end Hindman168
