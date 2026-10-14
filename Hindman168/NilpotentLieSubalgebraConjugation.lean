import Hindman168.NilpotentAdjoint
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Tower

/-! Every actual Lie subalgebra is preserved by conjugation with the
exponential of any of its associative-nilpotent elements. Lie-bracket closure
and finite rational scalar sums suffice; associative product closure is not
required. -/

namespace Hindman168
open Module

variable {R A : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [Algebra ℚ A]
local instance nilpotentAmbientLieRing : LieRing A := LieRing.ofAssociativeRing

 omit [Algebra ℚ R] in
 theorem commutatorEndQ_pow_mem (V : LieSubalgebra R A) {x y : A}
    (hx : x ∈ V) (hy : y ∈ V) (k : ℕ) : (commutatorEndQ x ^ k) y ∈ V := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hy
  | succ k ih =>
    rw [pow_succ']
    change commutatorEndQ x ((commutatorEndQ x ^ k) y) ∈ V
    rw [commutatorEndQ_apply]
    exact V.lie_mem hx ih

 theorem exp_commutatorEndQ_mem (V : LieSubalgebra R A) {x y : A}
    (hx : x ∈ V) (hy : y ∈ V) : IsNilpotent.exp (commutatorEndQ x) y ∈ V := by
  unfold IsNilpotent.exp
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply V.toSubmodule.sum_mem
  intro k _
  exact (V.toSubmodule.restrictScalars ℚ).smul_mem _ (commutatorEndQ_pow_mem V hx hy k)

 theorem lieSubalgebra_nilpotent_exp_conjugation_mem (V : LieSubalgebra R A) {x y : A}
    (hx : x ∈ V) (hn : IsNilpotent x) (hy : y ∈ V) :
    IsNilpotent.exp x * y * IsNilpotent.exp (-x) ∈ V := by
  rw [← exp_commutatorEndQ_apply hn y]
  exact exp_commutatorEndQ_mem V hx hy

 theorem lieSubalgebra_nilpotent_exp_conjugation_iff (V : LieSubalgebra R A) {x : A}
    (hx : x ∈ V) (hn : IsNilpotent x) (y : A) :
    IsNilpotent.exp x * y * IsNilpotent.exp (-x) ∈ V ↔ y ∈ V := by
  constructor
  · intro hy
    have hi := lieSubalgebra_nilpotent_exp_conjugation_mem V (V.neg_mem hx) hn.neg hy
    have heq : IsNilpotent.exp (-x) * (IsNilpotent.exp x * y * IsNilpotent.exp (-x)) *
        IsNilpotent.exp (-(-x)) = y := by
      rw [neg_neg]
      calc
        _ = (IsNilpotent.exp (-x) * IsNilpotent.exp x) * y *
            (IsNilpotent.exp (-x) * IsNilpotent.exp x) := by simp only [mul_assoc]
        _ = y := by rw [IsNilpotent.exp_neg_mul_exp_self hn, one_mul, mul_one]
    exact heq ▸ hi
  · exact lieSubalgebra_nilpotent_exp_conjugation_mem V hx hn

end Hindman168
