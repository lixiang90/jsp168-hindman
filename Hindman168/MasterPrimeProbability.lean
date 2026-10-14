import Hindman168.MasterPrimeStage
import Hindman168.PrimeGoodSamples

/-!
# Nonvanishing and distinctness for the sequential arithmetic stages

The probability bounds apply to the actual chosen pool at each stage,
including arbitrary earlier histories and the recursively generated ones.
The small-prime divisibility exception is proved separately in
MasterSmallPrimeProbability and packaged by MasterParameterFamily.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem masterStagePolynomialFamilyZero_rapid {n : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    RapidlySmall atTop (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) (fun w =>
      primePolynomialFamilyZeroMass (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper D) := by
  exact growingPrimePolynomialFamilyZeroMass_rapid
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w))) D hD

theorem masterStageRepeated_rapid {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (n : ℕ) :
    RapidlySmall atTop (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) (fun w =>
      primeRepeatedMass n (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper) := by
  exact growingPrimeRepeatedMass_rapid
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w))) n

theorem masterStageBadSample_rapid {n : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    RapidlySmall atTop (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) (fun w =>
      primeBadSampleMass (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper D) := by
  exact growingPrimeBadSampleMass_rapid
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w))) D hD

theorem masterStageGoodSample_tendsto_one {n : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    Tendsto (fun w => primeGoodSampleMass (masterStagePool w (e0 w) (M w) (history w)).lower
      (masterStagePool w (e0 w) (M w) (history w)).upper D) atTop (𝓝 1) := by
  exact growingPrimeGoodSampleMass_tendsto_one
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w))) D hD

theorem masterStage_exists_good_eventually {n : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    ∀ᶠ w in atTop, ∃ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper) ∧
      Function.Injective x ∧ ∀ p ∈ D,
        MvPolynomial.eval (fun i => (x i : ℤ)) p ≠ 0 ∧
        (M w : ℕ) * (MvPolynomial.eval (fun i => (x i : ℤ)) p).natAbs ∣
          masterStageGap w (e0 w) (M w) D (history w) := by
  have hg := growingPrimePool_exists_good_eventually
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w))) D hD
  filter_upwards [hg] with w hw
  obtain ⟨x, hx, hinj, hzero⟩ := hw
  refine ⟨x, hx, hinj, fun p hp => ⟨hzero p hp, ?_⟩⟩
  exact masterStageGap_value_dvd w (e0 w) (M w) (history w) hp hx (hzero p hp)

theorem masterPrimeHistory_exists_good_eventually {n : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0) (l : ℕ) :
    ∀ᶠ w in atTop, ∃ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool
        (masterStagePool w (e0 w) (M w) (masterPrimeHistory w (e0 w) (M w) D l)).lower
        (masterStagePool w (e0 w) (M w) (masterPrimeHistory w (e0 w) (M w) D l)).upper) ∧
      Function.Injective x ∧ ∀ p ∈ D,
        MvPolynomial.eval (fun i => (x i : ℤ)) p ≠ 0 ∧
        (M w : ℕ) * (MvPolynomial.eval (fun i => (x i : ℤ)) p).natAbs ∣
          masterStageGap w (e0 w) (M w) D (masterPrimeHistory w (e0 w) (M w) D l) :=
  masterStage_exists_good_eventually D hD

end Hindman168
