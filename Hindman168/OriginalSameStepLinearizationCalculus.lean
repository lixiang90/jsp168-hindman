import OAI.Combinatorics.Progressions.Compatibility.TensorInduction
import OAI.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.LinearAlgebra.Basis.Prod
/-!
# Small polynomial calculus for same-step linearization

Derived from OpenAI math, fixed commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0.
The complete upstream source remains under dependencies/openai-finite-szemeredi.
Upstream paths below are relative to lean/OAI/Combinatorics/Progressions:
- `Estimates/ShiftedGradedCalculus.lean`, lines 152–172.
- `Polynomial/PolynomialShiftStructure.lean`, lines 101–132.
- `Estimates/ShiftedGradedCalculus.lean`, lines 182–200.
- `Estimates/ShiftedGradedCalculus.lean`, lines 319–334.
- `Estimates/ShiftedGradedCalculus.lean`, lines 522–527.
- `Fourier/BohrNiltestBudget.lean`, lines 18–73.

Modifications: The declarations are moved to independent local namespaces, and field notation for the moved maps is made explicit. Tensor induction uses the proven compatibility alias. The original filtration and adapted polynomial types are reused unchanged.
No assumptions or mathematical conclusions are added or removed.
-/
namespace Hindman168.OriginalSameStepLinearization.Calculus
open OAI.Erdos3 OAI.Erdos3.VectorPolynomial
open scoped TensorProduct BigOperators
variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
theorem coefficients_pderiv (i : σ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  induction p using TensorProduct.inductionOn with
  | tmul q x =>
    rw [LinearMap.rTensor_tmul]
    rw [coefficients_tmul, coefficients_tmul]
    change (MvPolynomial.pderiv i q).coeff α • x =
      (α i + 1 : ℚ) • (q.coeff (α + Finsupp.single i 1) • x)
    rw [MvPolynomial.coeff_pderiv, smul_smul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq, smul_add]

theorem coefficients_directionalDerivative [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (directionalDerivative h p) α =
      ∑ i, h i • ((α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1)) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, coefficients_pderiv]

theorem pderiv_commute (i j : σ) (p : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L
        ((MvPolynomial.pderiv j).toLinearMap.rTensor L p) =
      (MvPolynomial.pderiv j).toLinearMap.rTensor L
        ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  apply coefficients.injective
  ext α
  simp only [coefficients_pderiv, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij),
    Nat.add_zero, smul_smul]
  congr 1
  · ring
  · congr 1
    abel

theorem directionalDerivative_commute [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative h (directionalDerivative k p) =
      directionalDerivative k (directionalDerivative h p) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_commute, mul_comm]

variable {s : ℕ} (F : NilpotentLieFiltration L s)
theorem directionalDerivative_mem_shifted [Fintype σ] (h : σ → ℚ) (k : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 1) := by
  intro α
  rw [coefficients_directionalDerivative]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  have hi := hp (α + Finsupp.single i 1)
  simpa only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc] using hi

theorem directionalDerivative_mem_next [Fintype σ] (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    directionalDerivative h p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 1 := by
  apply directionalDerivative_mem_shifted F h 0
  intro α
  simpa only [Nat.add_zero] using p.property α


variable [Fintype σ] (h : σ → ℚ)

noncomputable def adaptedDirectionalDerivative :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ((directionalDerivative h).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra (fun _ => 1)).toSubmodule (by
      intro p α
      exact F.antitone (Nat.le_succ _) (directionalDerivative_mem_next F h p α))

@[simp] theorem adaptedDirectionalDerivative_coe (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (adaptedDirectionalDerivative F h p : VectorPolynomial σ ℚ L) = directionalDerivative h p.val := rfl

theorem adaptedDirectionalDerivative_mem_shifted (k : ℕ)
    {p : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hp : p ∈ F.shiftedPolynomialIdeal (fun _ => 1) k) :
    adaptedDirectionalDerivative F h p ∈ F.shiftedPolynomialIdeal (fun _ => 1) (k + 1) :=
  directionalDerivative_mem_shifted F h k hp

theorem adaptedDirectionalDerivative_lie (p q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    adaptedDirectionalDerivative F h ⁅p, q⁆ =
      ⁅adaptedDirectionalDerivative F h p, q⁆ + ⁅p, adaptedDirectionalDerivative F h q⁆ := by
  apply Subtype.ext
  exact directionalDerivative_lie h p.val q.val

end Hindman168.OriginalSameStepLinearization.Calculus

namespace Hindman168.OriginalSameStepLinearization.TimeTorus
open OAI.Erdos3 Module
def Algebra (d : ℕ) := Fin d → ℚ

instance (d : ℕ) : AddCommGroup (Algebra d) :=
  inferInstanceAs (AddCommGroup (Fin d → ℚ))

instance (d : ℕ) : Module ℚ (Algebra d) :=
  inferInstanceAs (Module ℚ (Fin d → ℚ))

instance (d : ℕ) : LieRing (Algebra d) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Fin d → ℚ))
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance (d : ℕ) : LieAlgebra ℚ (Algebra d) where
  toModule := inferInstanceAs (Module ℚ (Fin d → ℚ))
  lie_smul _ _ _ := by
    change (0 : Algebra d) = _ • (0 : Algebra d)
    exact (smul_zero _).symm

theorem lie_eq_zero {d : ℕ} (x y : Algebra d) : ⁅x, y⁆ = 0 := rfl

noncomputable def basis (d : ℕ) : Basis (Fin d) ℚ (Algebra d) := by
  change Basis (Fin d) ℚ (Fin d → ℚ)
  exact Pi.basisFun ℚ (Fin d)

theorem basis_repr (d : ℕ) (x : Algebra d) (i : Fin d) : (basis d).repr x i = x i := by
  change Fin d → ℚ at x
  exact Pi.basisFun_repr ℚ (Fin d) x i

theorem basis_equivFun (d : ℕ) (x : Algebra d) : (basis d).equivFun x = x := by
  ext i
  exact basis_repr d x i

theorem basis_equivFun_symm (d : ℕ) (x : Fin d → ℚ) : (basis d).equivFun.symm x = x := by
  have h := basis_equivFun d ((basis d).equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def filtration (d : ℕ) : NilpotentLieFiltration (Algebra d) 1 where
  layer j := if j ≤ 1 then ⊤ else ⊥
  antitone := by
    intro i j hij
    by_cases hj : j ≤ 1
    · have hi := hij.trans hj
      simp only [hi, hj, ite_true, le_refl]
    · simp only [hj, ite_false, bot_le]
  one_eq_top := by simp
  lie_mem := by
    intro i j a b _ _
    rw [lie_eq_zero]
    exact Submodule.zero_mem _
  terminal := by simp

end Hindman168.OriginalSameStepLinearization.TimeTorus
