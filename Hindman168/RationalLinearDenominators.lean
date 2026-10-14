import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.Algebra.Group.Quotient

/-! Clearing rational denominators in an actual integer submodule. Rational
real subspaces are defined relative to this submodule, not by a compactness
hypothesis. This is the linear part of the rational-layer argument; it does
not identify a nilpotent group lattice with its additive logarithms. -/

namespace Hindman168
open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Every vector in the rational span has a nonzero integer multiple in the
original integer submodule. No finite generation is needed. -/
theorem rationalSpan_integer_multiple (L : Submodule ℤ E) {x : E}
    (hx : x ∈ span ℚ (L : Set E)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    apply L.add_mem
    · simpa [mul_smul, mul_comm n m] using L.smul_mem m hnx
    · simpa [mul_smul] using L.smul_mem n hmy
  | smul r x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n * (r.den : ℤ), mul_ne_zero hn (by exact_mod_cast r.den_ne_zero), ?_⟩
    have hr : (r.den : ℚ) * r = r.num := by
      calc (r.den : ℚ) * r = (r.den : ℚ) * ((r.num : ℚ) / r.den) :=
             congrArg ((r.den : ℚ) * ·) r.num_div_den.symm
           _ = (r.num : ℚ) := by field_simp
    have heq : (n * (r.den : ℤ)) • (r • x) = r.num • (n • x) := by
      simp only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_mul, Int.cast_natCast,
        smul_smul]
      congr 1
      calc (n : ℚ) * r.den * r = n * ((r.den : ℚ) * r) := by ring
           _ = (r.num : ℚ) * n := by rw [hr]; ring
    rw [heq]
    exact L.smul_mem _ hnx

end Hindman168
