import Hindman168.ScalarNonlinearRationalPeriod
import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLieRationalPowerMembership

/-! TRUE rational polynomial factors have actual period M*q modulo the
ORIGINAL lattice and representatives in ONE fixed finite family. Only
Exp(y)^q is required in Gamma; Exp(y) itself is not asserted lattice. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_direction_integer_power {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (y : D.E) (q : ℕ) (k : ℤ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((q : ℝ)*(k : ℝ)) • y) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q)^k := by
  have hv : ((q : ℝ)*(k : ℝ)) • y = (k : ℝ) • ((q : ℝ) • y) := by
    rw [smul_smul,mul_comm]
  calc
    _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((k : ℝ) • ((q : ℝ) • y)) :=
      congrArg (fun v : D.E => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) hv
    _ = (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((q : ℝ) • y))^k :=
      nativeLieExponential_int_smul (E := D.E) (I := D.I) (G := D.G) _ k
    _ = _ := congrArg (fun g : D.G => g^k) (nativeLieExponential_nat_smul (E := D.E) (I := D.I) (G := D.G) y q)

theorem native_rational_polynomial_progression_coset {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (D0 M q a t : ℕ) (z : ℕ → ℤ) (y : D.E)
    (hM : 0 < M) (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) :
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval ((a+M*q*t : ℕ) : ℝ) • y) : D.G ⧸ D.Γ) =
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ) := by
  obtain ⟨k,hk⟩ := scalar_nonlinear_rational_progression_period D0 M q a t z hM
  have he : (scalarNonlinearRationalPart D0 M z).eval ((a+M*q*t : ℕ) : ℝ) =
      (scalarNonlinearRationalPart D0 M z).eval (a : ℝ)+(q : ℝ)*(k : ℝ) := by linarith
  have hGroup : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval ((a+M*q*t : ℕ) : ℝ) • y) =
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

theorem native_rational_polynomial_finite_residue {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (D0 M q : ℕ) (z : ℕ → ℤ) (y : D.E)
    (hM : 0 < M) (hq : 0 < q)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) (n : ℕ) :
    ∃ m ∈ Finset.range (M*q),
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        ((scalarNonlinearRationalPart D0 M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ) := by
  obtain ⟨m,k,hm,hScalar⟩ := scalar_nonlinear_rational_finite_residue D0 M q n z hM hq
  have he : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((scalarNonlinearRationalPart D0 M z).eval (n : ℝ) • y) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)*
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q)^k := by
    calc
      _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (((m : ℝ)/(M : ℝ)+(q : ℝ)*(k : ℝ)) • y) :=
        congrArg (fun r : ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (r • y)) hScalar
      _ = _ := (nativeLieExponential_add_smul (E := D.E) (I := D.I) (G := D.G) y _ _).trans
        (congrArg (fun g : D.G => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)*g)
          (native_rational_direction_integer_power D y q k))
  refine ⟨m,Finset.mem_range.mpr hm,?_⟩
  symm
  apply QuotientGroup.eq.mpr
  rw [he]
  simpa only [inv_mul_cancel_left] using D.Γ.zpow_mem hpow k

end Hindman168
