import Hindman168.PredictionQuotientLengths
import Hindman168.MasterCyclicShortLengths

namespace Hindman168
open Filter
open scoped Topology Classical

theorem masterPredictionModulus_cap {N r b L : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin b → Fin N) (primeGap : ℕ → Fin r → Fin L)
    (J : ℕ) (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ (F.modulus w : ℕ))
    (hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (primeGap w j).val = (gap w q).val) :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      ∀ q, J * (predictionCubeModulus w (s w q) (f q) x).natAbs ≤
        ((F.pool w (gap w q).val).upper + F.auxiliary w (gap w q).val) ^
          (J + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1) := by
  filter_upwards [hs, hslots] with w hsw hslot
  intro x hx q
  apply predictionCubeModulus_polynomial_cap
  · have ha := F.auxiliary_ge_two w (gap w q).val
    omega
  · exact (Nat.le_of_dvd (F.modulus w).pos (hsw q)).trans
      ((F.modulus_le_auxiliary _ _).trans (Nat.le_add_left _ _))
  · intro j hj
    have hv := masterPrimeSlotsMass_support F w (fun j => primeGap w j) hx j
    rw [hslot q j hj] at hv
    omega


end Hindman168
