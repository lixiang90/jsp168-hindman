import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Two-branch tensor induction compatibility

The fixed OpenAI source `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
uses the two-branch `TensorProduct.inductionOn` interface.  This file supplies
that interface from the three-branch eliminator in the pinned Lean 4.32.2
Mathlib dependency.  The zero case follows from the pure tensor `0 ⊗ₜ 0`;
no additional mathematical assumption is introduced.
-/

namespace TensorProduct

open scoped TensorProduct

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

@[elab_as_elim]
protected theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  exact TensorProduct.induction_on (motive := motive) z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add

end TensorProduct
