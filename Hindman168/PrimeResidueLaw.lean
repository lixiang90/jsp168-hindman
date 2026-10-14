import Hindman168.PrimeHarmonicAP
import Hindman168.UniformFiniteMass

/-!
# Actual prime-pool residue laws converge to uniform primitive residues

The L1 distance is the paper's sum of absolute coefficients. For a pool
above q, every prime is a q-unit, so the support outside primitive classes
is exactly zero. Both the actual pushed PMF and its finite real mass are
identified. The modulus is fixed before choosing the dyadic cutoff.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

def primeUnitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => q.Coprime a)

theorem primeUnitResidues_mem {q a : ℕ} :
    a ∈ primeUnitResidues q ↔ a < q ∧ a.Coprime q := by
  simp only [primeUnitResidues, Finset.mem_filter, Finset.mem_range, Nat.coprime_comm]

theorem primeUnitResidues_card (q : ℕ) : (primeUnitResidues q).card = q.totient := rfl

noncomputable def primeUnitUniformMass (q : ℕ) : FiniteMass.Mass ℕ :=
  FiniteMass.flatMass (primeUnitResidues q) (1 / q.totient)

theorem primeUnitUniformMass_nonneg (q a : ℕ) : 0 ≤ primeUnitUniformMass q a :=
  FiniteMass.flatMass_nonneg _ (one_div_nonneg.mpr (Nat.cast_nonneg _)) a

theorem primeUnitUniformMass_total {q : ℕ} (hq : 1 ≤ q) :
    FiniteMass.total (primeUnitUniformMass q) = 1 := by
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  rw [primeUnitUniformMass, FiniteMass.flatMass_total, primeUnitResidues_card]
  field_simp

theorem primeUnitUniformMass_support (q : ℕ) :
    (primeUnitUniformMass q).support ⊆ primeUnitResidues q := FiniteMass.flatMass_support _ _

noncomputable def primePoolResidueMass (q A B : ℕ) : FiniteMass.Mass ℕ :=
  (primePoolMass A B).mapDomain (fun p => p % q)

theorem primePoolResidueMass_apply (q A B a : ℕ) :
    primePoolResidueMass q A B a =
      primeHarmonicResidue q a A B / primePoolHarmonicMass A B := by
  rw [primePoolResidueMass, FiniteMass.push_apply,
    Finset.sum_subset (primePoolMass_support A B) (by
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp]
      split_ifs <;> rfl)]
  have he : ∀ p ∈ primePool A B,
      (if a = p % q then primePoolMass A B p else 0) =
        (if p % q = a then (p : ℝ)⁻¹ else 0) / primePoolHarmonicMass A B := by
    intro p hp
    rw [primePoolMass_apply, primePoolWeight, if_pos hp]
    by_cases hpa : p % q = a
    · rw [if_pos hpa.symm, if_pos hpa]
    · rw [if_neg (Ne.symm hpa), if_neg hpa, zero_div]
  rw [Finset.sum_congr rfl he, ← Finset.sum_div]
  rfl

theorem primePoolResidueMass_nonneg (q A B a : ℕ) : 0 ≤ primePoolResidueMass q A B a :=
  FiniteMass.push_nonneg _ _ (primePoolMass_nonneg A B) a

theorem primePoolResidueMass_total {A B : ℕ} (q : ℕ)
    (hH : 0 < primePoolHarmonicMass A B) : FiniteMass.total (primePoolResidueMass q A B) = 1 := by
  rw [primePoolResidueMass, FiniteMass.total_push, primePoolMass_total hH]

theorem primePoolResidueMass_support {q A B : ℕ} (hq : 1 ≤ q) (hA : q < A) :
    (primePoolResidueMass q A B).support ⊆ primeUnitResidues q := by
  intro a ha
  by_contra hn
  have hz : primePoolResidueMass q A B a = 0 := by
    apply Finsupp.mapDomain_of_not_mem_image_support
    rintro ⟨p, hp, he⟩
    have hmem := primePool_mem.mp (primePoolMass_support A B hp)
    have hpq : q < p := hA.trans_le hmem.1
    have hpc : p.Coprime q := hmem.2.2.coprime_iff_not_dvd.mpr
      (fun hd => (Nat.le_of_dvd hq hd).not_gt hpq)
    have hmod : (p % q).Coprime q := by
      change (p % q).gcd q = 1
      rw [(Nat.mod_modEq p q).gcd_eq]
      exact hpc
    apply hn
    rw [← he]
    exact primeUnitResidues_mem.mpr ⟨Nat.mod_lt p hq, hmod⟩
  exact (Finsupp.mem_support_iff.mp ha) hz

theorem primePoolResiduePMF_apply (q A B a : ℕ)
    (hH : 0 < primePoolHarmonicMass A B) :
    ((primePoolPMF A B hH).map (fun p => p % q)) a =
      ENNReal.ofReal (primeHarmonicResidue q a A B / primePoolHarmonicMass A B) := by
  rw [primePoolPMF, FiniteMass.toPMF_map_apply]
  rw [← primePoolResidueMass_apply]
  rfl

theorem primePoolResidueMass_distance {q A B : ℕ} (hq : 1 ≤ q) (hA : q < A) :
    FiniteMass.distance (primePoolResidueMass q A B) (primeUnitUniformMass q) =
      ∑ a ∈ primeUnitResidues q,
        |primeHarmonicResidue q a A B / primePoolHarmonicMass A B - 1 / q.totient| := by
  have hs : (primePoolResidueMass q A B - primeUnitUniformMass q).support ⊆
      primeUnitResidues q := by
    intro a ha
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with ha | ha
    · exact primePoolResidueMass_support hq hA ha
    · exact primeUnitUniformMass_support q ha
  rw [FiniteMass.distance, FiniteMass.variation_eq_sum _ hs]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.sub_apply, primePoolResidueMass_apply, primeUnitUniformMass,
    FiniteMass.flatMass_apply, if_pos ha]

theorem primePoolResidueMass_dyadic_small {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, FiniteMass.distance
      (primePoolResidueMass q (2 ^ n) (2 ^ (n + 1))) (primeUnitUniformMass q) ≤ ε := by
  let η : ℝ := ε / q.totient
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hη : 0 < η := div_pos hε hφ
  have hu : ∀ a ∈ primeUnitResidues q, a.Coprime q ∧ a < q := fun a ha =>
    ⟨(primeUnitResidues_mem.mp ha).2, (primeUnitResidues_mem.mp ha).1⟩
  filter_upwards [primeHarmonicResidue_dyadic_uniform_small (primeUnitResidues q) hq hu hη,
    dyadic_atTop.eventually (eventually_ge_atTop (q + 1))] with n he hn
  rw [primePoolResidueMass_distance hq (by omega : q < 2 ^ n)]
  calc
    _ ≤ ∑ a ∈ primeUnitResidues q, η := Finset.sum_le_sum he
    _ = ε := by rw [Finset.sum_const, nsmul_eq_mul, primeUnitResidues_card]; dsimp [η]; field_simp

theorem primePoolResidueMass_dyadic_tendsto {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => FiniteMass.distance
      (primePoolResidueMass q (2 ^ n) (2 ^ (n + 1))) (primeUnitUniformMass q)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => lt_of_lt_of_le hb (FiniteMass.variation_nonneg _))
  · intro b hb
    have hε : (0 : ℝ) < b / 2 := by linarith
    filter_upwards [primePoolResidueMass_dyadic_small hq hε] with n hn
    linarith

end Hindman168
