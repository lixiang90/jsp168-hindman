import Hindman168.WeightedShearGroup
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Homeomorph.Defs

/-!
The nilpotent weighted-shear group acts on the actual coordinate cover.
Inverse substitution fixes the contravariance of polynomial evaluation.
Every coordinate map `x_i ↦ x_i + p_i(x)` of strictly lower weighted degree
is realized by an element of this single, dimension-independent group.
-/

namespace Hindman168
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedShear_aeval_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (x : σ → R) (p : MvPolynomial σ R) :
    MvPolynomial.aeval x (f p) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (f (X i))) p := by
  have h : (MvPolynomial.aeval x).comp f =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (f (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h p

/-- The coordinate action dual to inverse polynomial substitution. -/
def weightedShearPoint (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R)
    (x : σ → R) : σ → R :=
  fun i => MvPolynomial.aeval x (f.symm (X i))

@[simp] theorem weightedShearPoint_one (x : σ → R) :
    weightedShearPoint (1 : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) x = x := by
  funext i
  exact MvPolynomial.aeval_X x i

theorem weightedShearPoint_mul
    (f g : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) (x : σ → R) :
    weightedShearPoint (f*g) x = weightedShearPoint f (weightedShearPoint g x) := by
  funext i
  exact weightedShear_aeval_comp g.symm.toAlgHom x (f.symm (X i))

/-- A genuine action on the coordinate cover, available to the finite recurrence theorem. -/
instance weightedShearPointAction (w : σ → ℕ) :
    MulAction (weightedShearGroup (R := R) w) (σ → R) where
  smul f x := weightedShearPoint f.val x
  one_smul := weightedShearPoint_one
  mul_smul f g x := weightedShearPoint_mul f.val g.val x

/-- The actual shear with given displacement polynomials, as an element of the common group. -/
noncomputable def weightedShearOfDisplacements (w : σ → ℕ)
    (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)) :
    weightedShearGroup (R := R) w := by
  let f := weightedShearSubstitutionEquiv (MvPolynomial.aeval (fun i => X i+p i))
    (weightedShearSubstitution_aeval w p hp)
  have hf : WeightedShearSubstitution w 1 f.toAlgHom :=
    weightedShearSubstitution_aeval w p hp
  exact ⟨f.symm, weightedShearSubstitution_inv hf⟩

/-- Evaluation of the group action is exactly the original coordinate shear. -/
theorem weightedShearOfDisplacements_smul (w : σ → ℕ)
    (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1))
    (x : σ → R) (i : σ) :
    (weightedShearOfDisplacements w p hp • x) i =
      x i + MvPolynomial.eval x (p i) := by
  change MvPolynomial.aeval x
    (MvPolynomial.aeval (fun j => X j+p j) (X i)) = _
  simp only [MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_eq_eval]

/-- Every polynomial shear on the actual coordinate cover is bijective. -/
theorem weightedShearMap_bijective (w : σ → ℕ)
    (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)) :
    Function.Bijective (fun x : σ → R => fun i => x i+MvPolynomial.eval x (p i)) := by
  have h : (fun x : σ → R => fun i => x i+MvPolynomial.eval x (p i)) =
      fun x => weightedShearOfDisplacements w p hp • x := by
    funext x i
    exact (weightedShearOfDisplacements_smul w p hp x i).symm
  rw [h]
  exact MulAction.bijective _

/-- Every group element acts by another shear of exactly the original weighted type. -/
theorem weightedShearPoint_displacements (w : σ → ℕ)
    (f : weightedShearGroup (R := R) w) :
    ∃ p : σ → MvPolynomial σ R,
      (∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)) ∧
      ∀ x i, (f • x) i = x i+MvPolynomial.eval x (p i) := by
  let p : σ → MvPolynomial σ R := fun i => f.val.symm (X i)-X i
  refine ⟨p, weightedShearSubstitution_inv f.property, ?_⟩
  intro x i
  change MvPolynomial.aeval x (f.val.symm (X i)) =
    x i+MvPolynomial.eval x (f.val.symm (X i)-X i)
  simp only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_sub, MvPolynomial.eval_X]
  abel

section Topological
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem weightedShearPoint_continuous
    (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) :
    Continuous (weightedShearPoint f) := by
  apply continuous_pi
  intro i
  exact MvPolynomial.continuous_eval (f.symm (X i))

/-- A weighted shear is an actual homeomorphism of the coordinate cover. -/
def weightedShearPointHomeomorph (w : σ → ℕ)
    (f : weightedShearGroup (R := R) w) : (σ → R) ≃ₜ (σ → R) where
  toFun := fun x => f • x
  invFun := fun x => f⁻¹ • x
  left_inv x := inv_smul_smul f x
  right_inv x := smul_inv_smul f x
  continuous_toFun := weightedShearPoint_continuous f.val
  continuous_invFun := weightedShearPoint_continuous f.val⁻¹

end Topological
end
end Hindman168
