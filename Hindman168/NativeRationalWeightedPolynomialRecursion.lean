import Hindman168.NativeRationalWeightedPolynomialState

/-! Finite ACTUAL polynomial recursion, choosing compact representatives at
every true relative/terminal stage. It retains actual original pair samples;
its termination does not assert discrepancy or character reconstruction. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeIteratedRationalWeightedPolynomialReduction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) :
    ℕ → Σ m : ℕ, NativeRationalWeightedPolynomialState.{u} s m
  | 0 => ⟨ℓ,nativeRationalWeightedPolynomialInitial D F p hp⟩
  | n+1 =>
      let prev := nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n
      ⟨prev.1-1,nativeRationalWeightedPolynomialStep prev.2 (shifts n)⟩

theorem native_rational_weighted_polynomial_recursion_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) (n : ℕ) :
    (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n).1 = ℓ-n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n).1-1 = ℓ-(n+1)
      rw [ih,Nat.sub_sub]

theorem native_rational_weighted_polynomial_recursion_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) (n : ℕ) :
    RoughVectorMvDegreeLE (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n).2.2.2.val (ℓ-n) := by
  rw [← native_rational_weighted_polynomial_recursion_bound D F p hp shifts n]
  exact (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n).2.2.2.property.2

theorem native_rational_weighted_polynomial_recursion_step_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) (j : ℕ) (n : ℤ) :
    nativeMvPolynomialOrbit (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts (j+1)).2.1
      (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts (j+1)).2.2.2.val (fun _ => n) =
    nativeRationalTerminalFactorMap
      (nativeRationalRelativeData (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1
        (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.1 1)
      (nativeRelativeRationalLieFiltration (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1
        (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.1)
      ((nativeRationalCompactNormalizedIntegerPair (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1
        (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.1
        (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.2.val
        (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.2.property.1 (shifts j) n) :
        (nativeRationalRelativeData (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1
          (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.1 1).G ⧸
        (nativeRationalRelativeData (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1
          (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.2.1 1).Γ) :=
  native_rational_weighted_polynomial_step_sample
    (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2 (shifts j) n

theorem native_rational_weighted_polynomial_recursion_terminal_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) :
    Subsingleton (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.1.G := by
  have hf : NativeRationalLieFiltration (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.1 0 := by
    have he := (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.2.1
    simpa only [native_rational_weighted_polynomial_recursion_bound,Nat.sub_self] using he
  exact native_rational_degree_zero_group_subsingleton _ hf

theorem native_rational_weighted_polynomial_recursion_terminal_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (shifts : ℕ → ℤ) (x : Unit → ℤ) :
    nativeMvPolynomialOrbit (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.1
      (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.2.2.val x =
    (1 : (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts ℓ).2.1.G) := by
  letI := native_rational_weighted_polynomial_recursion_terminal_group D F p hp shifts
  apply congrArg QuotientGroup.mk
  exact Subsingleton.elim _ _

end Hindman168
