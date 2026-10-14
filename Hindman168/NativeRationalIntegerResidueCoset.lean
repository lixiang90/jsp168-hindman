import Hindman168.ScalarNonlinearIntegerPeriod
import Hindman168.NativeRationalPolynomialFiniteResidues

/-! SAME actual original integer residue class gives CONSTANT rational
factor right coset, for any two original integer samples. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_polynomial_integer_modEq_coset {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (D0 M q : ℕ) (a n : ℤ) (z : ℕ → ℤ) (y : D.E)
    (hM : 0 < M) (hCong : Int.ModEq ((M*q : ℕ) : ℤ) a n)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) :
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ)=
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ) := by
  obtain ⟨k,hk⟩ := scalar_nonlinear_rational_integer_modEq_period D0 M q a n z hM hCong
  have he : (scalarNonlinearRationalPart D0 M z).eval (n : ℝ)=
      (scalarNonlinearRationalPart D0 M z).eval (a : ℝ)+(q : ℝ)*(k : ℝ) := by linarith
  have hGroup : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval (n : ℝ) • y)=
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        ((scalarNonlinearRationalPart D0 M z).eval (a : ℝ) • y)*
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q)^k := by
    calc
      _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (((scalarNonlinearRationalPart D0 M z).eval (a : ℝ)+(q : ℝ)*(k : ℝ)) • y) :=
        congrArg (fun r : ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (r • y)) he
      _ = _ := (nativeLieExponential_add_smul (E := D.E) (I := D.I) (G := D.G) y _ _).trans
        (congrArg (fun g : D.G => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          ((scalarNonlinearRationalPart D0 M z).eval (a : ℝ) • y)*g)
            (native_rational_direction_integer_power D y q k))
  symm
  apply QuotientGroup.eq.mpr
  rw [hGroup]
  simpa only [inv_mul_cancel_left] using D.Γ.zpow_mem hpow k

end Hindman168
