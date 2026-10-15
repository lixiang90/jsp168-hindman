import Hindman168.FiniteComplexMean
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Expect

/-! Exact one-dimensional support and mean transport for the original
interval inverse. The complex mean identity also holds at length zero. -/

namespace Hindman168
open scoped BigOperators Classical

def originalInverseIntervalPoint {L : ℕ} (n : Fin L) : Unit → ℤ :=
  fun _ => (n.val : ℤ)

theorem originalInverseIntervalPoint_injective (L : ℕ) :
    Function.Injective (@originalInverseIntervalPoint L) := by
  intro a b hab
  have he := congrFun hab ()
  change (a.val : ℤ) = (b.val : ℤ) at he
  apply Fin.ext
  exact_mod_cast he

noncomputable def originalInverseInterval (L : ℕ) : Finset (Unit → ℤ) :=
  Finset.univ.image (@originalInverseIntervalPoint L)

theorem originalInverseInterval_mem {L : ℕ} (x : Unit → ℤ) :
    x ∈ originalInverseInterval L ↔ 0 ≤ x () ∧ x () < (L : ℤ) := by
  constructor
  · intro hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ (n.val : ℤ) ∧ (n.val : ℤ) < (L : ℤ)
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast n.isLt⟩
  · intro hx
    let n : Fin L := ⟨(x ()).toNat, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_univ _, ?_⟩
    funext u
    cases u
    exact Int.toNat_of_nonneg hx.1

@[simp] theorem originalInverseInterval_card (L : ℕ) :
    (originalInverseInterval L).card = L := by
  rw [originalInverseInterval,
    Finset.card_image_of_injective _ (originalInverseIntervalPoint_injective L)]
  simp

theorem originalInverseInterval_nonempty {L : ℕ} (hL : 0 < L) :
    (originalInverseInterval L).Nonempty := by
  apply Finset.card_pos.mp
  simpa using hL

theorem originalInverseInterval_sum (L : ℕ) (F : (Unit → ℤ) → ℂ) :
    (∑ x ∈ originalInverseInterval L, F x) =
      ∑ n : Fin L, F (originalInverseIntervalPoint n) := by
  rw [originalInverseInterval, Finset.sum_image]
  intro a _ b _ hab
  exact originalInverseIntervalPoint_injective L hab

theorem originalInverseInterval_mean (L : ℕ) (F : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ originalInverseInterval L, F x) =
      finiteComplexMean (fun n : Fin L => F (originalInverseIntervalPoint n)) := by
  rw [Finset.expect_eq_sum_div_card, originalInverseInterval_sum,
    originalInverseInterval_card]
  simp only [finiteComplexMean, Fintype.card_fin]

theorem originalInverseInterval_periodic_mean (q L : ℕ) (v : ZMod q → ℝ)
    (T : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ originalInverseInterval L, (v (x () : ZMod q) : ℂ) * T x) =
      finiteComplexMean (fun n : Fin L =>
        (v (n.val : ZMod q) : ℂ) * T (originalInverseIntervalPoint n)) := by
  simpa only [originalInverseIntervalPoint, Int.cast_natCast] using
    originalInverseInterval_mean L (fun x => (v (x () : ZMod q) : ℂ) * T x)

/-- Pair-sum reflection for the doubled interval modulus. No primality
or oddness of the modulus is required. -/
theorem originalInverseInterval_pair_sums {L : ℕ} (hL : 0 < L)
    (a b c d : ℤ)
    (ha : 0 ≤ a ∧ a < (L : ℤ)) (hb : 0 ≤ b ∧ b < (L : ℤ))
    (hc : 0 ≤ c ∧ c < (L : ℤ)) (hd : 0 ≤ d ∧ d < (L : ℤ))
    (he : ((a + b : ℤ) : ZMod (2 * L)) = ((c + d : ℤ) : ZMod (2 * L))) :
    a + b = c + d := by
  letI : NeZero (2 * L) := ⟨by omega⟩
  have hab : 0 ≤ a + b ∧ a + b < ((2 * L : ℕ) : ℤ) := by
    push_cast
    omega
  have hcd : 0 ≤ c + d ∧ c + d < ((2 * L : ℕ) : ℤ) := by
    push_cast
    omega
  have hv := congrArg (fun z : ZMod (2 * L) => (z.val : ℤ)) he
  rw [ZMod.val_intCast, ZMod.val_intCast,
    Int.emod_eq_of_lt hab.1 hab.2, Int.emod_eq_of_lt hcd.1 hcd.2] at hv
  exact hv

end Hindman168
