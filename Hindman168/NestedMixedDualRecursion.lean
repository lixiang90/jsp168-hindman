import Hindman168.MixedDualRecursion
import Hindman168.MixedDualProductClosure

namespace Hindman168
open scoped BigOperators Classical

/-- The actual lower-order coefficient with two independently chosen shifts. -/
noncomputable def subgroupMixedDualRecursiveCoefficient {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ)
    (f : Finset (Fin (d + 1)) → G → ℝ) (a b x : G) : ℝ :=
  subgroupMixedDualFunction Q d (fun ω y =>
    f (ω.image Fin.succ) (y + a) * f (insert 0 (ω.image Fin.succ)) (y + b)) x

theorem subgroupMixedDualRecursiveCoefficient_abs_le_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ)
    (f : Finset (Fin (d + 1)) → G → ℝ)
    (hf : ∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1) (a b x : G) :
    |subgroupMixedDualRecursiveCoefficient Q d f a b x| ≤ 1 := by
  apply subgroupMixedDualFunction_abs_le_one
  intro ω hω y
  have him : ω.image Fin.succ ≠ ∅ := fun h => hω (Finset.image_eq_empty.mp h)
  rw [abs_mul]
  exact (mul_le_mul (hf _ him _) (hf _ (by simp) _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem subgroupMixedDualRecursiveCoefficient_zero {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : Finset (Fin 1) → G → ℝ) (a b x : G) :
    subgroupMixedDualRecursiveCoefficient Q 0 f a b x = 1 := by
  have he : (Finset.univ : Finset (Finset (Fin 0))).erase ∅ = ∅ := by decide
  simp only [subgroupMixedDualRecursiveCoefficient, subgroupMixedDualFunction, he,
    Finset.prod_empty, finiteHaarMean_const]

/-- Product of the shifted coefficients in the two-level dual recursion. -/
noncomputable def subgroupNestedMixedDualCoefficient {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] (d e : ℕ)
    (f : Finset (Fin (d + 1)) → G → ℝ) (u : Finset (Fin (e + 1)) → G → ℝ)
    (n m h j x : G) : ℝ :=
  subgroupMixedDualRecursiveCoefficient Q d f n h (x + m) *
    subgroupMixedDualRecursiveCoefficient R e u m j (x + h)

/-- Exact finite-subgroup counterpart of the double recursive expansion.
Only the distinguished outer input must be an actual second-direction dual. -/
theorem subgroupMixedDualFunction_nested_translate_expansion {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] (d e : ℕ)
    (f : Finset (Fin (d + 1)) → G → ℝ) (u : Finset (Fin (e + 1)) → G → ℝ)
    (hf : ∀ y, f {0} y = subgroupMixedDualFunction R (e + 1) u y)
    (n : Q) (m : R) (x : G) :
    subgroupMixedDualFunction Q (d + 1) f (x + n + m) =
      finiteHaarMean (fun h : Q => finiteHaarMean (fun j : R =>
        subgroupNestedMixedDualCoefficient Q R d e f u n m h j x *
          u {0} (x + h + j))) := by
  rw [add_right_comm x (n : G) (m : G),
    subgroupMixedDualFunction_subgroup_translate_expansion Q d f n (x + m)]
  congr 1
  funext h
  rw [hf, add_right_comm x (m : G) (h : G),
    subgroupMixedDualFunction_subgroup_translate_expansion R e u m (x + h)]
  rw [← finiteHaarMean_mul_const]
  congr 1
  funext j
  dsimp only [subgroupNestedMixedDualCoefficient, subgroupMixedDualRecursiveCoefficient]
  ring

theorem subgroupNestedMixedDualCoefficient_abs_le_one {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] (d e : ℕ)
    (f : Finset (Fin (d + 1)) → G → ℝ) (u : Finset (Fin (e + 1)) → G → ℝ)
    (hf : ∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1)
    (hu : ∀ ω, ω ≠ ∅ → ∀ x, |u ω x| ≤ 1) (n m h j x : G) :
    |subgroupNestedMixedDualCoefficient Q R d e f u n m h j x| ≤ 1 := by
  rw [subgroupNestedMixedDualCoefficient, abs_mul]
  exact (mul_le_mul (subgroupMixedDualRecursiveCoefficient_abs_le_one Q d f hf n h _)
    (subgroupMixedDualRecursiveCoefficient_abs_le_one R e u hu m j _)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Hindman168
