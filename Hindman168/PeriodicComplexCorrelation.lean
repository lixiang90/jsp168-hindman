import Hindman168.FiniteComplexMean
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Basic

namespace Hindman168
open scoped BigOperators Classical

theorem finiteComplexMean_fin_mul (K q : ℕ) (f : ℕ → ℂ) :
    finiteComplexMean (fun n : Fin (K * q) => f n.val) =
      finiteComplexMean (fun j : Fin K =>
        finiteComplexMean (fun z : Fin q => f (j.val * q + z.val))) := by
  rw [← finiteComplexMean_equiv (finProdFinEquiv : Fin K × Fin q ≃ Fin (K * q)),
    finiteComplexMean_prod]
  congr 1
  funext j
  congr 1
  funext z
  congr 1
  change z.val + q * j.val = j.val * q + z.val
  ac_rfl

/-- The periodic input retains its original cyclic representative in every
period; the correlator itself is allowed to be entirely nonperiodic. -/
theorem periodic_complex_correlation_split (K q : ℕ) [NeZero q]
    (v : ZMod q → ℂ) (ψ : ℕ → ℂ) :
    finiteComplexMean (fun n : Fin (K * q) => v (n.val : ZMod q) * ψ n.val) =
      finiteComplexMean (fun j : Fin K => finiteComplexMean (fun z : Fin q =>
        v (z.val : ZMod q) * ψ (j.val * q + z.val))) := by
  rw [finiteComplexMean_fin_mul K q (fun n => v (n : ZMod q) * ψ n)]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

theorem periodic_complex_correlation_extract (K q : ℕ) [NeZero q] (hK : 0 < K)
    (v : ZMod q → ℂ) (ψ : ℕ → ℂ) (δ : ℝ)
    (hδ : δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
      v (n.val : ZMod q) * ψ n.val)‖) :
    ∃ j : Fin K, δ ≤ ‖finiteComplexMean (fun z : Fin q =>
      v (z.val : ZMod q) * ψ (j.val * q + z.val))‖ := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  rw [periodic_complex_correlation_split] at hδ
  obtain ⟨j, hj⟩ := finiteComplexMean_exists_norm_ge (fun j : Fin K =>
    finiteComplexMean (fun z : Fin q => v (z.val : ZMod q) * ψ (j.val * q + z.val)))
  exact ⟨j, hδ.trans hj⟩

end Hindman168
