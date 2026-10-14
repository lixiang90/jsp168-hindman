import Hindman168.NativeRationalUnitInverse
import Hindman168.ScalarMvLinePolynomial
import Hindman168.ScalarUnitPolynomial

/-! ACTUAL native short-line sources are CONSTRUCTED from the original
vector polynomial. True rational filtration weights, exact ALL-real values,
INTEGER quotient samples and literal scalar line coefficients are proved. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalLineScalarMap {κ : Type*} (x : κ → ℤ) (q : κ → ℕ) :
    MvPolynomial κ ℝ →+* MvPolynomial Unit ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j =>
    MvPolynomial.C (x j : ℝ)+MvPolynomial.C (q j : ℝ)*MvPolynomial.X ())

noncomputable def nativeRationalLinePolynomial {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E) (x : κ → ℤ) (q : κ → ℕ) :
    RoughVectorMvPolynomial Unit D.E :=
  p.map (fun term => (nativeRationalLineScalarMap x q term.1,term.2))

theorem native_rational_line_scalar_map_degree {κ : Type*} (x : κ → ℤ) (q : κ → ℕ)
    (P : MvPolynomial κ ℝ) : (nativeRationalLineScalarMap x q P).totalDegree ≤ P.totalDegree := by
  apply rough_mv_linear_substitution_degree
  intro j
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by rw [MvPolynomial.totalDegree_C]; omega)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X])

theorem native_rational_line_polynomial_weighted {s ℓ : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial κ D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (x : κ → ℤ) (q : κ → ℕ) :
    RoughVectorMvWeightedDegree L.layer (nativeRationalLinePolynomial D p x q) 0 := by
  intro term ht
  obtain ⟨old,hOld,rfl⟩ := List.mem_map.mp ht
  exact L.antitone (Nat.add_le_add_right (native_rational_line_scalar_map_degree x q old.1) 0) (hp old hOld)

theorem native_rational_line_scalar_map_eval {κ : Type*} (x : κ → ℤ) (q : κ → ℕ)
    (P : MvPolynomial κ ℝ) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (nativeRationalLineScalarMap x q P) =
      MvPolynomial.eval (fun j => (x j : ℝ)+(q j : ℝ)*t) P := by
  dsimp only [nativeRationalLineScalarMap]
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun y => MvPolynomial.eval y P)
  funext j
  simp

theorem native_rational_line_polynomial_eval {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (x : κ → ℤ) (q : κ → ℕ) (t : ℝ) :
    roughVectorMvEval (nativeRationalLinePolynomial D p x q) (fun _ => t) =
      roughVectorMvEval p (fun j => (x j : ℝ)+(q j : ℝ)*t) := by
  induction p with
  | nil => simp [nativeRationalLinePolynomial,roughVectorMvEval]
  | cons term p ih =>
    change MvPolynomial.eval (fun _ => t) (nativeRationalLineScalarMap x q term.1) • term.2+
      roughVectorMvEval (nativeRationalLinePolynomial D p x q) (fun _ => t) = _
    rw [native_rational_line_scalar_map_eval,ih]
    rfl

theorem native_rational_line_polynomial_orbit {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (x : κ → ℤ) (q : κ → ℕ) (t : ℤ) :
    nativeMvPolynomialOrbit D (nativeRationalLinePolynomial D p x q) (fun _ => t) =
      nativeMvPolynomialOrbit D p (fun j => x j+(q j : ℤ)*t) := by
  rw [nativeMvPolynomialOrbit,nativeMvPolynomialOrbit,native_rational_line_polynomial_eval]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]

theorem native_rational_line_polynomial_scalar {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (χ : D.E →ₗ[ℝ] ℝ) (x : κ → ℤ) (q : κ → ℕ) :
    scalarUnitPolynomial (roughVectorMvProjection χ (nativeRationalLinePolynomial D p x q)) =
      scalarMvLinePolynomial (roughVectorMvProjection χ p) (fun j => (x j : ℝ)) (fun j => (q j : ℝ)) := by
  apply Polynomial.funext
  intro t
  rw [scalar_unit_polynomial_eval,roughVectorMvProjection_eval,native_rational_line_polynomial_eval,
    scalar_mv_line_polynomial_eval,roughVectorMvProjection_eval]

theorem native_rational_line_polynomial_coefficient {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (χ : D.E →ₗ[ℝ] ℝ) (x : κ → ℤ) (q : κ → ℕ) (r : ℕ) :
    MvPolynomial.coeff (Finsupp.single () r)
      (roughVectorMvProjection χ (nativeRationalLinePolynomial D p x q)) =
      MvPolynomial.eval (fun j => (x j : ℝ))
        (scalarMvLineCoefficient (roughVectorMvProjection χ p) (fun j => (q j : ℝ)) r) := by
  rw [← scalar_unit_polynomial_coefficient,native_rational_line_polynomial_scalar,
    scalar_mv_line_polynomial_coefficient]

end Hindman168
