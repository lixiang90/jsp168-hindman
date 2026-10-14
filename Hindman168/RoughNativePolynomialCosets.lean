import Hindman168.RoughNativeResidueCosets
import Mathlib.Algebra.MvPolynomial.Eval

namespace Hindman168

theorem rough_integer_polynomial_modEq {κ : Type*} (P : MvPolynomial κ ℤ)
    (K : ℤ) (x y : κ → ℤ) (hxy : ∀ i, Int.ModEq K (x i) (y i)) :
    Int.ModEq K (MvPolynomial.eval x P) (MvPolynomial.eval y P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; exact Int.ModEq.refl a
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hxy i)

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_integer_polynomial_coset {κ : Type*}
    (Γ : Subgroup G) (V : E) (K : ℕ)
    (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (P : MvPolynomial κ ℤ) (x y : κ → ℤ)
    (hxy : ∀ i, Int.ModEq (K : ℤ) (x i) (y i)) :
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
      (((MvPolynomial.eval x P : ℤ) : ℝ) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
          (((MvPolynomial.eval y P : ℤ) : ℝ) • V)) :=
  rough_native_exponential_modEq Γ V K hK _ _ (rough_integer_polynomial_modEq P _ x y hxy)

end Hindman168
