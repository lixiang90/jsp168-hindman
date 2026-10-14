import Hindman168.DyadicRegularCoprimality
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic

/-!
# Actual rough parts and common-prime events

The list of prime factors retains every multiplicity. Filtering it at w
and taking its product gives the actual rough part of a nonzero value.
The zero case is explicit and is excluded in the polynomial event.
-/

namespace Hindman168

open scoped BigOperators Classical

def roughPartNat (w n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.primeFactorsList.filter (fun p => decide (w < p))).prod

theorem prime_dvd_natListProd_iff {q : ℕ} (hq : q.Prime) (l : List ℕ) :
    q ∣ l.prod ↔ ∃ p ∈ l, q ∣ p := by
  induction l with
  | nil => simp [Nat.dvd_one, hq.ne_one]
  | cons p l ih => simp [List.prod_cons, hq.dvd_mul, ih]

theorem roughPartNat_pos {w n : ℕ} (hn : n ≠ 0) : 0 < roughPartNat w n := by
  rw [roughPartNat, if_neg hn]
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro hp
  exact (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).ne' rfl

theorem prime_dvd_roughPartNat {w n q : ℕ} (hn : n ≠ 0) (hq : q.Prime) :
    q ∣ roughPartNat w n ↔ w < q ∧ q ∣ n := by
  rw [roughPartNat, if_neg hn, prime_dvd_natListProd_iff hq]
  constructor
  · rintro ⟨p, hp, hqp⟩
    have hp' : p ∈ n.primeFactorsList := List.mem_of_mem_filter hp
    have hpp := Nat.prime_of_mem_primeFactorsList hp'
    have he : q = p := (Nat.dvd_prime hpp).mp hqp |>.resolve_left hq.ne_one
    subst p
    exact ⟨by simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hp).2,
      Nat.dvd_of_mem_primeFactorsList hp'⟩
  · rintro ⟨hwq, hqn⟩
    refine ⟨q, ?_, dvd_refl q⟩
    exact List.mem_filter.mpr ⟨(Nat.mem_primeFactorsList hn).mpr ⟨hq, hqn⟩, by simpa using hwq⟩

theorem roughPartNat_not_coprime_iff {w a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ (roughPartNat w a).Coprime (roughPartNat w b) ↔
      ∃ q : ℕ, q.Prime ∧ w < q ∧ q ∣ a ∧ q ∣ b := by
  rw [Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨q, hq, hqa, hqb⟩
    obtain ⟨hwq, hqa'⟩ := (prime_dvd_roughPartNat ha hq).mp hqa
    exact ⟨q, hq, hwq, hqa', ((prime_dvd_roughPartNat hb hq).mp hqb).2⟩
  · rintro ⟨q, hq, hwq, hqa, hqb⟩
    exact ⟨q, hq, (prime_dvd_roughPartNat ha hq).mpr ⟨hwq, hqa⟩,
      (prime_dvd_roughPartNat hb hq).mpr ⟨hwq, hqb⟩⟩

theorem roughPartNat_gcd_gt_one_iff {w a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    1 < (roughPartNat w a).gcd (roughPartNat w b) ↔
      ∃ q : ℕ, q.Prime ∧ w < q ∧ q ∣ a ∧ q ∣ b := by
  have hz : 0 < (roughPartNat w a).gcd (roughPartNat w b) :=
    Nat.gcd_pos_of_pos_left _ (roughPartNat_pos ha)
  rw [← roughPartNat_not_coprime_iff ha hb, Nat.Coprime]
  omega

def commonPrimeEvent {m n : ℕ} (w : ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : Prop :=
  MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ≠ 0 ∧
    MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G ≠ 0 ∧
    ∃ q : ℕ, q.Prime ∧ w < q ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G

theorem commonPrimeEvent_rough_gcd_iff {m n w : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) :
    commonPrimeEvent w F G xy ↔
      MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ≠ 0 ∧
      MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G ≠ 0 ∧
      1 < (roughPartNat w (MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F).natAbs).gcd
        (roughPartNat w (MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G).natAbs) := by
  unfold commonPrimeEvent
  by_cases hF : MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F = 0
  · simp only [hF, ne_eq, not_true_eq_false, false_and]
  by_cases hG : MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G = 0
  · simp only [hG, ne_eq, not_true_eq_false, false_and, and_false]
  rw [roughPartNat_gcd_gt_one_iff (Int.natAbs_ne_zero.mpr hF) (Int.natAbs_ne_zero.mpr hG)]
  simp only [Int.natCast_dvd]

theorem commonPrimeEvent_swap {m n w : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) :
    commonPrimeEvent w F G xy ↔ commonPrimeEvent w G F xy.swap := by
  unfold commonPrimeEvent
  simp only [Prod.swap]
  tauto

end Hindman168
