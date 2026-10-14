import Hindman168.RationalPolynomialIntegerDilation
import Hindman168.UnitriangularPolynomialBCHCurve

/-! One positive integer simultaneously clears the actual exponential curves
of any finite family of rational strict matrices. Every integer parameter
then lies in the original integer unitriangular lattice after real casting.
These are genuine group lattice points, not an assumed additive log lattice. -/

noncomputable section
namespace Hindman168
open Matrix Polynomial

variable {n : ℕ}

 def unitriangularRationalExponentialCurve (A : StrictUpperTriangular n ℚ) :
    Unitriangular n (Polynomial ℚ) :=
  unitriangularExponential (unitriangularPolynomialScale A)

 theorem unitriangularRationalExponentialCurve_eval (A : StrictUpperTriangular n ℚ) (r : ℚ) :
    unitriangularMap (Polynomial.evalRingHom r) (unitriangularRationalExponentialCurve A) =
      unitriangularExponential (r • A) := by
  unfold unitriangularRationalExponentialCurve
  rw [unitriangularExponential_map, unitriangularPolynomialScale_eval]

 theorem unitriangularRationalExponentialCurve_constant (A : StrictUpperTriangular n ℚ)
    (i j : Fin n) :
    (((unitriangularRationalExponentialCurve A).val : Matrix (Fin n) (Fin n) (Polynomial ℚ))
      i j).coeff 0 = (1 : Matrix (Fin n) (Fin n) ℚ) i j := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h := congrArg (fun g : Unitriangular n ℚ =>
    (g.val : Matrix (Fin n) (Fin n) ℚ) i j)
    (unitriangularRationalExponentialCurve_eval A 0)
  change (((unitriangularRationalExponentialCurve A).val :
    Matrix (Fin n) (Fin n) (Polynomial ℚ)) i j).eval 0 = _ at h
  have hE : unitriangularExponential (0 : StrictUpperTriangular n ℚ) = 1 := by
    apply unitriangular_val_injective
    exact matrixFiniteExp_zero
  rw [zero_smul, hE] at h
  exact h

 theorem rational_unitriangular_integer_real_iff (g : Unitriangular n ℚ) :
    unitriangularMap (algebraMap ℚ ℝ) g ∈ integerUnitriangularLattice n ↔
      ∀ i j, (g.val : Matrix (Fin n) (Fin n) ℚ) i j ∈ (Int.castRingHom ℚ).range := by
  constructor
  · intro hg i j
    obtain ⟨z, hz⟩ := integerUnitriangularLattice_entry hg i j
    refine ⟨z, ?_⟩
    change (z : ℚ) = (g.val : Matrix (Fin n) (Fin n) ℚ) i j
    apply (algebraMap ℚ ℝ).injective
    change (z : ℝ) = (g.val : Matrix (Fin n) (Fin n) ℚ) i j
    exact hz.symm
  · intro hg
    apply (integerUnitriangularLattice_mem_iff_coordinates _).mpr
    intro p
    obtain ⟨z, hz⟩ := hg (unitriangularRow p) (unitriangularColumn p)
    refine ⟨z, ?_⟩
    change algebraMap ℚ ℝ ((g.val : Matrix (Fin n) (Fin n) ℚ)
      (unitriangularRow p) (unitriangularColumn p)) = (z : ℝ)
    rw [← hz]
    simp

 theorem unitriangular_rational_exponential_family_integer_dilation
    {ι : Type*} [Fintype ι] (A : ι → StrictUpperTriangular n ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i (z : ℤ),
      unitriangularMap (algebraMap ℚ ℝ)
        (unitriangularExponential (((D : ℚ) * z) • A i)) ∈ integerUnitriangularLattice n := by
  let p : (ι × Fin n × Fin n) → Polynomial ℚ := fun x =>
    ((unitriangularRationalExponentialCurve (A x.1)).val :
      Matrix (Fin n) (Fin n) (Polynomial ℚ)) x.2.1 x.2.2
  have h0 : ∀ x, (p x).coeff 0 ∈ (Int.castRingHom ℚ).range := by
    intro x
    change (((unitriangularRationalExponentialCurve (A x.1)).val :
      Matrix (Fin n) (Fin n) (Polynomial ℚ)) x.2.1 x.2.2).coeff 0 ∈ _
    rw [unitriangularRationalExponentialCurve_constant, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨D, hD, hp⟩ := rational_polynomial_family_integer_dilation p h0
  refine ⟨D, hD, ?_⟩
  intro i z
  apply (rational_unitriangular_integer_real_iff _).mpr
  intro a b
  have he := congrArg (fun g : Unitriangular n ℚ =>
    (g.val : Matrix (Fin n) (Fin n) ℚ) a b)
    (unitriangularRationalExponentialCurve_eval (A i) ((D : ℚ) * z))
  change (p (i, a, b)).eval ((D : ℚ) * z) = _ at he
  rw [← he]
  exact hp (i, a, b) z

 theorem strictUpperTriangularMap_rat_smul (r : ℚ) (A : StrictUpperTriangular n ℚ) :
    strictUpperTriangularMap (algebraMap ℚ ℝ) (r • A) =
      (r : ℝ) • strictUpperTriangularMap (algebraMap ℚ ℝ) A := by
  apply Subtype.ext
  ext i j
  change algebraMap ℚ ℝ (r * A.val i j) = (r : ℝ) * algebraMap ℚ ℝ (A.val i j)
  exact map_mul _ _ _

 theorem unitriangular_rational_exponential_family_lattice
    {ι : Type*} [Fintype ι] (A : ι → StrictUpperTriangular n ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i (z : ℤ),
      unitriangularExponential (((D : ℝ) * z) •
        strictUpperTriangularMap (algebraMap ℚ ℝ) (A i)) ∈ integerUnitriangularLattice n := by
  obtain ⟨D, hD, hp⟩ := unitriangular_rational_exponential_family_integer_dilation A
  refine ⟨D, hD, ?_⟩
  intro i z
  have h := hp i z
  rw [unitriangularExponential_map, strictUpperTriangularMap_rat_smul] at h
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] using h

 theorem unitriangular_rational_exponential_lattice (A : StrictUpperTriangular n ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ z : ℤ,
      unitriangularExponential (((D : ℝ) * z) •
        strictUpperTriangularMap (algebraMap ℚ ℝ) A) ∈ integerUnitriangularLattice n := by
  obtain ⟨D, hD, hp⟩ := unitriangular_rational_exponential_family_lattice
    (fun _ : Unit => A)
  exact ⟨D, hD, hp ()⟩

end Hindman168
