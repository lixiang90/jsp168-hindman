import Hindman168.ResidueRowReduction

/-!
# Normalized local kernel factors at the maximum row valuation

The global base modulus is exactly the product of all row divisors. CRT
initially gives local base exponent equal to the sum of the row valuations.
Actual quotient invariance reduces that exponent to their maximum, giving
the local factors used in the paper. Empty row families have maximum zero.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def rowMaxValuation {q : ℕ} (a : Fin q → ℕ) : ℕ := Finset.univ.sup a

theorem rowValuation_le_max {q : ℕ} (a : Fin q → ℕ) (u : Fin q) :
    a u ≤ rowMaxValuation a := Finset.le_sup (Finset.mem_univ u)

theorem rowMaxValuation_le_sum {q : ℕ} (a : Fin q → ℕ) : rowMaxValuation a ≤ ∑ u, a u := by
  apply Finset.sup_le_iff.mpr
  intro u _
  exact Finset.single_le_sum (fun v _ => Nat.zero_le (a v)) (Finset.mem_univ u)

theorem rowPrimePower_divisor_product {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (q : ℕ) (a : ι → Fin q → ℕ) :
    (∏ u, ∏ i, p i ^ a i u) = ∏ i, p i ^ (∑ u, a i u) := by
  rw [Finset.prod_comm]
  simp only [Finset.prod_pow_eq_pow_sum]

theorem normalized_primePower_kernel_crt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (q d : ℕ) (a : ι → Fin q → ℕ)
    [NeZero (∏ i, p i ^ (∑ u, a i u))]
    (hc : Pairwise (fun i j => (p i ^ (∑ u, a i u)).Coprime (p j ^ (∑ u, a j u))))
    (c : Fin q → Fin d → ℤ) :
    ((∏ u, ∏ i, p i ^ a i u : ℕ) : ℝ) *
      event (uniformFintypeMass (Fin d → ZMod (∏ i, p i ^ (∑ u, a i u))))
        (fun x => residueRowSystem (∏ i, p i ^ (∑ u, a i u)) q d (fun u => ∏ i, p i ^ a i u)
          (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun i _ =>
            pow_dvd_pow (p i) ((rowValuation_le_max (a i) u).trans (rowMaxValuation_le_sum (a i))))) c x = 0) =
      ∏ i, primePowerLocalAlpha (p i) q d (rowMaxValuation (a i)) (a i)
        (rowValuation_le_max (a i)) c := by
  let m : ι → ℕ := fun i => p i ^ (∑ u, a i u)
  let b : ι → Fin q → ℕ := fun i u => p i ^ a i u
  have hb (i : ι) (u : Fin q) : b i u ∣ m i :=
    pow_dvd_pow (p i) ((rowValuation_le_max (a i) u).trans (rowMaxValuation_le_sum (a i)))
  have h := residueRowSystem_normalized_crt_mass m hc q d b hb c
  have hlocal (i : ι) :
      (((∏ u, b i u : ℕ) : ℝ) * event (uniformFintypeMass (Fin d → ZMod (m i)))
        (fun x => residueRowSystem (m i) q d (b i) (hb i) c x = 0)) =
        primePowerLocalAlpha (p i) q d (rowMaxValuation (a i)) (a i)
          (rowValuation_le_max (a i)) c := by
    calc
      _ = primePowerLocalAlpha (p i) q d (∑ u, a i u) (a i)
          (fun u => (rowValuation_le_max (a i) u).trans (rowMaxValuation_le_sum (a i))) c := by
        unfold b m primePowerLocalAlpha
        rw [Finset.prod_pow_eq_pow_sum]
        rfl
      _ = _ := primePowerLocalAlpha_base_invariance (p i) q d _ _
        (rowMaxValuation_le_sum (a i)) (a i) (rowValuation_le_max (a i)) c
  simpa only [hlocal] using h

end Hindman168
