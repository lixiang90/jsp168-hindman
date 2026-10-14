import Hindman168.ScalarMvIntegerCube
import Hindman168.FiniteComplexSetMean
import Mathlib.Algebra.MvPolynomial.Rename

/-! Exact variable equivalences retain original cube samples, finite means,
monomial coefficients and total multi-index weights. -/

namespace Hindman168
open scoped BigOperators
variable {σ τ : Type*}

def scalarVariableAssignmentEquiv (e : σ ≃ τ) (R : Type*) : (σ → R) ≃ (τ → R) where
  toFun := fun x j => x (e.symm j)
  invFun := fun y i => y (e i)
  left_inv := by intro x; funext i; simp only [Equiv.symm_apply_apply]
  right_inv := by intro y; funext j; simp only [Equiv.apply_symm_apply]

theorem scalar_variable_equiv_apply (e : σ ≃ τ) {R : Type*} (x : σ → R) (j : τ) :
    scalarVariableAssignmentEquiv e R x j = x (e.symm j) := rfl

theorem scalar_variable_equiv_sum [Fintype σ] [Fintype τ] (e : σ ≃ τ) (J : σ → ℕ) :
    (∑ j, scalarVariableAssignmentEquiv e ℕ J j) = ∑ i, J i := by
  symm
  exact Fintype.sum_equiv e J (scalarVariableAssignmentEquiv e ℕ J)
    (fun i => by simp only [scalar_variable_equiv_apply,Equiv.symm_apply_apply])

theorem scalar_variable_equiv_finsupp [Fintype σ] [Fintype τ] (e : σ ≃ τ) (J : σ → ℕ) :
    Finsupp.equivFunOnFinite.symm (scalarVariableAssignmentEquiv e ℕ J) =
      (Finsupp.equivFunOnFinite.symm J).mapDomain e := by
  classical
  ext j
  obtain ⟨i,rfl⟩ := e.surjective j
  simp only [Finsupp.coe_equivFunOnFinite_symm,scalar_variable_equiv_apply,Equiv.symm_apply_apply,
    Finsupp.mapDomain_apply e.injective]

theorem scalar_variable_equiv_coefficient [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (p : MvPolynomial σ ℝ) (J : σ → ℕ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (scalarVariableAssignmentEquiv e ℕ J))
      (MvPolynomial.rename e p) = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p := by
  rw [scalar_variable_equiv_finsupp,MvPolynomial.coeff_rename_mapDomain e e.injective]

theorem scalar_variable_equiv_integer_cube [Fintype σ] [Fintype τ] (e : σ ≃ τ) (N : ℕ) :
    scalarMvIntegerCube τ N = (scalarMvIntegerCube σ N).image (scalarVariableAssignmentEquiv e ℤ) := by
  classical
  ext y
  rw [Finset.mem_image]
  constructor
  · intro hy
    refine ⟨fun i => y (e i),?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      exact fun i => (Fintype.mem_piFinset.mp hy) (e i)
    · funext j
      simp only [scalar_variable_equiv_apply,Equiv.apply_symm_apply]
  · rintro ⟨x,hx,rfl⟩
    apply Fintype.mem_piFinset.mpr
    exact fun j => (Fintype.mem_piFinset.mp hx) (e.symm j)

theorem scalar_variable_equiv_cube_mean [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (N : ℕ) (f : (τ → ℤ) → ℂ) :
    finiteComplexSetMean (scalarMvIntegerCube τ N) f =
      finiteComplexSetMean (scalarMvIntegerCube σ N) (fun x => f (scalarVariableAssignmentEquiv e ℤ x)) := by
  classical
  rw [scalar_variable_equiv_integer_cube e N]
  exact finiteComplexSetMean_image _ _ (scalarVariableAssignmentEquiv e ℤ).injective f

end Hindman168
