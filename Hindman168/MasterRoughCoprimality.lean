import Hindman168.RoughCoprimalityGoodEvents
import Hindman168.MasterParameterFamily

/-!
# Rough coprimality for the actual sequential master parameters

The existing growing-pool choice has lower exponent at least w, uniformly
over all previous histories and chosen stages. Thus the vanishing bad
events and probability-one rough-coprimality conclusions apply to the
actual constructed family, even with varying coordinate stage indices.
Its already-proved good-prime sample events provide concrete separate
conditioning events of probability tending to one.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem equidistributedGrowingPrimePool_lower_exponent_ge (V Q w : ℕ)
    (hQ : 1 ≤ Q) (hV : 1 ≤ V) :
    w ≤ (equidistributedGrowingPrimePool V Q w hQ).lowerExponent := by
  have hb := (equidistributedGrowingPrimePool_bounds V Q w hQ).2.1
  have hpow : 2 ^ w ≤ primePoolGrowthTarget V w := by
    have hp := Nat.pow_le_pow_left (by omega : 2 ≤ V + 1) w
    unfold primePoolGrowthTarget
    exact hp.trans (by simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right ((V + 1) ^ w) (Nat.succ_le_succ (Nat.zero_le w)))
  have h := hpow.trans hb
  change (2 : ℕ) ^ w ≤ 2 ^ (equidistributedGrowingPrimePool V Q w hQ).lowerExponent at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

theorem masterStagePool_lower_exponent_ge (w e0 : ℕ) (M : ℕ+) (history : MasterPrimeHistory) :
    w ≤ (masterStagePool w e0 M history).lowerExponent :=
  equidistributedGrowingPrimePool_lower_exponent_ge _ _ _ (masterStageModulus_pos _ _ _)
    (masterStageAuxiliary_ge_one M history)

theorem constructedMasterFamily_pool_lower_exponent_ge {a : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin a) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) (w l : ℕ) :
    w ≤ ((constructedMasterFamily N D hD).pool w l).lowerExponent :=
  masterStagePool_lower_exponent_ge _ _ _ _

theorem constructedMasterFamily_rough_good_tendsto_one {a m n : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin a) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (slotsF : ℕ → Fin m → ℕ) (slotsG : ℕ → Fin n → ℕ) :
    Tendsto (fun w => event
      (tensor (dyadicPoolTupleMass (fun i => (constructedMasterFamily N D hD).pool w (slotsF w i)))
        (dyadicPoolTupleMass (fun i => (constructedMasterFamily N D hD).pool w (slotsG w i))))
      (roughPolynomialGoodEvent w F G)) atTop (𝓝 1) := by
  exact dyadicPool_rough_good_tendsto_one hF hG _ _
    (fun w i => constructedMasterFamily_pool_lower_exponent_ge N D hD w (slotsF w i))
    (fun w i => constructedMasterFamily_pool_lower_exponent_ge N D hD w (slotsG w i))

theorem constructedMasterFamily_primeGoodSample_tendsto_one {a n : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin a) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0) (l : ℕ → ℕ) :
    Tendsto (fun w => event
      (dyadicPoolTupleMass (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w)))
      (primeSampleGood T)) atTop (𝓝 1) := by
  let family := constructedMasterFamily N D hD
  have hpool (w : ℕ) : family.pool w (l w) =
      masterStagePool w (family.exponent w) (family.modulus w)
        (masterPrimeHistory w (family.exponent w) (family.modulus w) D (l w)) := rfl
  change Tendsto (fun w => primeGoodSampleMass (family.pool w (l w)).lower
    (family.pool w (l w)).upper T) atTop (𝓝 1)
  simpa only [hpool] using masterStageGoodSample_tendsto_one
    (M := family.modulus) (e0 := family.exponent)
    (history := fun w => masterPrimeHistory w (family.exponent w) (family.modulus w) D (l w)) T hT

theorem constructedMasterFamily_goodSample_conditioned_rough_tendsto_one {a m n : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin a) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (TF : Finset (MvPolynomial (Fin m) ℤ)) (hTF : ∀ f ∈ TF, f ≠ 0)
    (TG : Finset (MvPolynomial (Fin n) ℤ)) (hTG : ∀ f ∈ TG, f ≠ 0)
    (lF lG : ℕ → ℕ) :
    Tendsto (fun w => event
      (tensor (conditionMass (dyadicPoolTupleMass
          (fun _ : Fin m => (constructedMasterFamily N D hD).pool w (lF w))) (primeSampleGood TF))
        (conditionMass (dyadicPoolTupleMass
          (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (lG w))) (primeSampleGood TG)))
      (roughPolynomialGoodEvent w F G)) atTop (𝓝 1) := by
  exact conditioned_dyadicPool_rough_good_tendsto_one hF hG _ _
    (fun w _ => constructedMasterFamily_pool_lower_exponent_ge N D hD w (lF w))
    (fun w _ => constructedMasterFamily_pool_lower_exponent_ge N D hD w (lG w)) _ _
    (constructedMasterFamily_primeGoodSample_tendsto_one N D hD TF hTF lF)
    (constructedMasterFamily_primeGoodSample_tendsto_one N D hD TG hTG lG)

end Hindman168
