import Mathlib.LinearAlgebra.Basis.Basic

namespace Hindman168
open Module

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem basis_layer_mem_iff_zero_coordinates (b : Basis ι R M) (p : ι → Prop)
    (V : Submodule R M) (hb : Submodule.span R (b '' {i | p i}) = V) (v : M) :
    v ∈ V ↔ ∀ i, ¬ p i → b.repr v i = 0 := by
  classical
  rw [← hb, b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  · intro h i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)

end Hindman168
