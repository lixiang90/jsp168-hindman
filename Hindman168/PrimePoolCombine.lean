import Hindman168.PrimeResidueLaw
import Hindman168.PrimePoolGrowth

/-!
# Complete dyadic unions preserve prime residue probability errors

The extension is by a harmonic-mass weighted average. Thus arbitrarily
many later dyadic intervals do not amplify the residue error. This lets
the divergent prime reciprocal sum supply arbitrary total mass after
fixing the modulus, lower cutoff, and requested L1 accuracy.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

theorem primePoolHarmonicMass_split {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    primePoolHarmonicMass A C = primePoolHarmonicMass A B + primePoolHarmonicMass B C := by
  rw [primePoolHarmonicMass_eq_tail (hAB.trans hBC), primePoolHarmonicMass_eq_tail hAB,
    primePoolHarmonicMass_eq_tail hBC]
  ring

theorem primeHarmonicResidue_split {A B C : ℕ} (q a : ℕ) (hAB : A ≤ B) (hBC : B ≤ C) :
    primeHarmonicResidue q a A C = primeHarmonicResidue q a A B + primeHarmonicResidue q a B C := by
  unfold primeHarmonicResidue primePool
  simp only [Finset.sum_filter]
  exact (Finset.sum_Ico_consecutive _ hAB hBC).symm

theorem normalized_error_add {r s H K c η : ℝ} (hH : 0 < H) (hK : 0 < K)
    (hr : |r / H - c| ≤ η) (hs : |s / K - c| ≤ η) :
    |(r + s) / (H + K) - c| ≤ η := by
  have hHK : 0 < H + K := add_pos hH hK
  have hiR : r / H - c = (r - H * c) / H := by field_simp
  have hiS : s / K - c = (s - K * c) / K := by field_simp
  rw [hiR, abs_div, abs_of_pos hH] at hr
  rw [hiS, abs_div, abs_of_pos hK] at hs
  have hr' := (div_le_iff₀ hH).mp hr
  have hs' := (div_le_iff₀ hK).mp hs
  have hi : (r + s) / (H + K) - c = ((r - H * c) + (s - K * c)) / (H + K) := by field_simp; ring
  rw [hi, abs_div, abs_of_pos hHK]
  apply (div_le_iff₀ hHK).mpr
  calc
    _ ≤ |r - H * c| + |s - K * c| := abs_add_le _ _
    _ ≤ η * H + η * K := add_le_add hr' hs'
    _ = η * (H + K) := by ring

def PrimePoolClassBound (q A B : ℕ) (η : ℝ) : Prop :=
  0 < primePoolHarmonicMass A B ∧ ∀ a ∈ primeUnitResidues q,
    |primeHarmonicResidue q a A B / primePoolHarmonicMass A B - 1 / q.totient| ≤ η

theorem PrimePoolClassBound.consecutive {q A B C : ℕ} {η : ℝ}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (h1 : PrimePoolClassBound q A B η) (h2 : PrimePoolClassBound q B C η) :
    PrimePoolClassBound q A C η := by
  rw [PrimePoolClassBound, primePoolHarmonicMass_split hAB hBC]
  refine ⟨add_pos h1.1 h2.1, ?_⟩
  intro a ha
  rw [primeHarmonicResidue_split q a hAB hBC]
  exact normalized_error_add h1.1 h2.1 (h1.2 a ha) (h2.2 a ha)

theorem PrimePoolClassBound.distance_le {q A B : ℕ} {η : ℝ}
    (hq : 1 ≤ q) (hA : q < A) (h : PrimePoolClassBound q A B η) :
    FiniteMass.distance (primePoolResidueMass q A B) (primeUnitUniformMass q) ≤ q.totient * η := by
  rw [primePoolResidueMass_distance hq hA]
  calc
    _ ≤ ∑ a ∈ primeUnitResidues q, η := Finset.sum_le_sum h.2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, primeUnitResidues_card]

theorem primePoolClassBound_dyadic_eventually {q : ℕ} (hq : 1 ≤ q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, PrimePoolClassBound q (2 ^ n) (2 ^ (n + 1)) η := by
  have hu : ∀ a ∈ primeUnitResidues q, a.Coprime q ∧ a < q := fun a ha =>
    ⟨(primeUnitResidues_mem.mp ha).2, (primeUnitResidues_mem.mp ha).1⟩
  exact primePoolHarmonicMass_dyadic_eventually_pos.and
    (primeHarmonicResidue_dyadic_uniform_small (primeUnitResidues q) hq hu hη)

theorem primePoolClassBound_dyadic_extend {q N a : ℕ} {η : ℝ}
    (hN : ∀ n, N ≤ n → PrimePoolClassBound q (2 ^ n) (2 ^ (n + 1)) η)
    (ha : N ≤ a) : ∀ k : ℕ, 0 < k → PrimePoolClassBound q (2 ^ a) (2 ^ (a + k)) η := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.add_zero] using hN a ha
    · have hcur := ih (Nat.pos_of_ne_zero hk0)
      have hnext := hN (a + k) (by omega)
      have hAB : 2 ^ a ≤ 2 ^ (a + k) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have hBC : 2 ^ (a + k) ≤ 2 ^ (a + k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hcur.consecutive hAB hBC hnext

theorem exists_dyadic_equidi_prime_pool {q : ℕ} (hq : 1 ≤ q) (L : ℕ) (H : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : DyadicPrimePool, q < P.lower ∧ L ≤ P.lower ∧ H ≤ P.harmonicMass ∧
      0 < P.harmonicMass ∧ FiniteMass.distance
        (primePoolResidueMass q P.lower P.upper) (primeUnitUniformMass q) ≤ ε := by
  let η : ℝ := ε / q.totient
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hη : 0 < η := div_pos hε hφ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (primePoolClassBound_dyadic_eventually hq hη)
  obtain ⟨a, haN, haL⟩ := ((eventually_ge_atTop N).and
    (dyadic_atTop.eventually (eventually_ge_atTop (max L (q + 1))))).exists
  obtain ⟨b, hab, hmass⟩ := exists_large_dyadic_prime_mass a H
  have hk : 0 < b - a := Nat.sub_pos_of_lt hab
  have hclass := primePoolClassBound_dyadic_extend hN haN (b - a) hk
  have he : a + (b - a) = b := Nat.add_sub_of_le hab.le
  rw [he] at hclass
  have hqa : q < 2 ^ a := by have hh := (le_max_right L (q + 1)).trans haL; omega
  refine ⟨⟨a, b, hab⟩, hqa, (le_max_left L (q + 1)).trans haL, hmass, hclass.1, ?_⟩
  have hd := hclass.distance_le hq hqa
  have hv : (q.totient : ℝ) * η = ε := by dsimp [η]; field_simp
  rwa [hv] at hd

end Hindman168
