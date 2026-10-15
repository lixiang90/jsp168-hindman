import Hindman168.OriginalSameStepLinearizationBasis
import Hindman168.OriginalSameStepLinearizationGrid
import OAI.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Finsupp.Defs
/-!
# Scalar extension of adapted polynomial coefficients

Derived from OpenAI math, fixed commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0.
Complete upstream source remains under dependencies/openai-finite-szemeredi.
Upstream paths relative to lean/OAI/Combinatorics/Progressions:
- Polynomial/RealGradedSymbolPolynomial.lean, lines 18–21, 54–60, 112–161, 173–179.
- Estimates/LowerStepSquare.lean, lines 302–310.
- Estimates/RealSymbolRepresentativeSplitting.lean, lines 255–260.
- Polynomial/RealAdaptedPolynomialGroup.lean, lines 293–373, 482.
Modifications: complete proof fragments moved to an independent namespace;
field notation is made explicit and the independently proven monomial basis is
used. The original filtration, adapted polynomial, scalar extension and BCH
group types are unchanged. No additional mathematical assumptions are used.
-/
namespace Hindman168.OriginalSameStepLinearization.Realization
open OAI.Erdos3 OAI.Erdos3.VectorPolynomial Module
open scoped TensorProduct
section Coordinates
variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
noncomputable def mixedCoordinates (b : Basis ι S V) :
    VectorPolynomial σ R V ≃ₗ[R] ((σ →₀ ℕ) × ι) →₀ S :=
  coefficients.trans ((Finsupp.mapRange.linearEquiv (b.repr.restrictScalars R)).trans
    (Finsupp.curryLinearEquiv R).symm)
noncomputable def supportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : VectorPolynomial σ R V →ₗ[R] A →₀ S :=
  (Finsupp.lsubtypeDomain A).comp (mixedCoordinates b).toLinearMap

@[simp] theorem supportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (p : VectorPolynomial σ R V) (z : A) :
    supportedCoordinates b A p z = b.repr (coefficients p z.val.1) z.val.2 := rfl
end Coordinates
section Lie
variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
section General

private theorem ring_zero_lie {K : Type*} [LieRing K] (x : K) : ⁅(0 : K), x⁆ = 0 := zero_lie x

private theorem ring_lie_zero {K : Type*} [LieRing K] (x : K) : ⁅x, (0 : K)⁆ = 0 := lie_zero x

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {N : Type*} [LieRing N] [LieAlgebra R N]

noncomputable def lieTensorLeftComm :
    (A ⊗[R] (B ⊗[R] N)) ≃ₗ⁅R⁆ (B ⊗[R] (A ⊗[R] N)) :=
  { TensorProduct.leftComm R A B N with
  map_lie' {x y} := by
    change TensorProduct.leftComm R A B N ⁅x, y⁆ =
      ⁅TensorProduct.leftComm R A B N x, TensorProduct.leftComm R A B N y⁆
    induction x using TensorProduct.inductionOn with
    | tmul a p =>
      induction y using TensorProduct.inductionOn with
      | tmul b q =>
        induction p using TensorProduct.inductionOn with
        | tmul f u =>
          induction q using TensorProduct.inductionOn with
          | tmul g v =>
            simp only [LieAlgebra.ExtendScalars.bracket_tmul, TensorProduct.leftComm_tmul]
          | add q r hq hr =>
            rw [TensorProduct.tmul_add, LieRing.lie_add, map_add, hq, hr, map_add, LieRing.lie_add]
        | add p q hp hq =>
          rw [TensorProduct.tmul_add, LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]
      | add y z hy hz => rw [LieRing.lie_add, map_add, hy, hz, map_add, LieRing.lie_add]
    | add x z hx hz => rw [LieRing.add_lie, map_add, hx, hz, map_add, LieRing.add_lie] }

end General

noncomputable def realificationLieEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) ≃ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  lieTensorLeftComm

@[simp] theorem realificationLieEquiv_tmul_tmul (a : ℝ) (p : MvPolynomial σ ℚ) (v : L) :
    realificationLieEquiv (a ⊗ₜ[ℚ] (p ⊗ₜ[ℚ] v)) = p ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v) :=
  TensorProduct.leftComm_tmul ℚ _ _ _

@[simp] theorem coefficients_realificationLieEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (realificationLieEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.inductionOn with
  | tmul f v =>
    rw [realificationLieEquiv_tmul_tmul, coefficients_tmul, coefficients_tmul,
      TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

theorem eval_realificationLieEquiv_tmul {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (r : ℝ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (realificationLieEquiv (r ⊗ₜ[ℚ] p)) = r ⊗ₜ[ℚ] eval x p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    rw [realificationLieEquiv_tmul_tmul, eval_tmul, eval_tmul, TensorProduct.tmul_smul]
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
end Lie
section Adapted
variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
theorem realLayer_eq_span_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) :
    (F.realLayer i).toSubmodule = Submodule.span ℝ (b.baseChange ℝ '' S) := by
  change (F.layer i).baseChange ℝ = _
  rw [hS, Submodule.baseChange_span, Set.image_image]
  congr 2
  funext j
  exact (Basis.baseChange_apply ℝ b j).symm


variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
include hlayers
theorem real_mem_layer_iff_basis_coordinates (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realification.layer j ↔ ∀ i, ¬ j ≤ ω i → (b.baseChange ℝ).repr v i = 0 := by
  change v ∈ (F.realLayer j).toSubmodule ↔ _
  rw [realLayer_eq_span_basis F b j {i | j ≤ ω i} (hlayers j), basis_mem_span_image_iff]
  rfl

end Adapted
section Map
variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)
noncomputable def realAdaptedPolynomialMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.adaptedLieSubalgebra w).incl)

@[simp] theorem realAdaptedPolynomialMap_coefficient_tmul
    (a : ℝ) (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (realAdaptedPolynomialMap F w (a ⊗ₜ[ℚ] p)) α =
      a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) α := by
  change coefficients (realificationLieEquiv
    (a ⊗ₜ[ℚ] (p : VectorPolynomial σ ℚ L))) α = _
  have hc := coefficients_realificationLieEquiv_tmul a (p : VectorPolynomial σ ℚ L) α
  convert hc using 2

theorem realAdaptedPolynomialMap_adapted (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realification.Adapted w (realAdaptedPolynomialMap F w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [realAdaptedPolynomialMap_coefficient_tmul F]
    exact LieSubmodule.tmul_mem_baseChange_of_mem a (p.property α)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

noncomputable def realAdaptedPolynomialTensor :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w where
  toLinearMap := (realAdaptedPolynomialMap F w).toLinearMap.codRestrict
    (F.realification.adaptedSubmodule w) (fun x =>
      (F.realification.mem_adaptedSubmodule w _).mpr (realAdaptedPolynomialMap_adapted F w x))
  map_lie' {x y} := by
    apply Subtype.ext
    exact (realAdaptedPolynomialMap F w).map_lie x y

@[simp] theorem realAdaptedPolynomialTensor_coe (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (realAdaptedPolynomialTensor F w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      realAdaptedPolynomialMap F w x := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedPolynomialTensor_coordinates
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (b.baseChange ℝ).repr (coefficients (realAdaptedPolynomialMap F w x) z.val.1) z.val.2 =
      ((BasisTools.adaptedMonomialBasis F b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [realAdaptedPolynomialMap_coefficient_tmul F, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, BasisTools.adaptedMonomialBasis_repr F]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

include b ω hlayers in
theorem realAdaptedPolynomialTensor_surjective :
    Function.Surjective (realAdaptedPolynomialTensor F w) := by
  intro p
  let c := supportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  let x := ((BasisTools.adaptedMonomialBasis F b ω hlayers w).baseChange ℝ).repr.symm c
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α ≤ ω i
  · have hc := realAdaptedPolynomialTensor_coordinates F w b ω hlayers x ⟨(α, i), h⟩
    change (b.baseChange ℝ).repr (coefficients (realAdaptedPolynomialMap F w x) α) i = _
    rw [hc]
    change (((BasisTools.adaptedMonomialBasis F b ω hlayers w).baseChange ℝ).repr
      (((BasisTools.adaptedMonomialBasis F b ω hlayers w).baseChange ℝ).repr.symm c)) ⟨(α, i), h⟩ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · have hleft := (real_mem_layer_iff_basis_coordinates F b ω hlayers _ _).mp
      ((F.realification.adapted_iff_coefficients w _).mp
        (realAdaptedPolynomialMap_adapted F w x) α) i h
    have hright := (real_mem_layer_iff_basis_coordinates F b ω hlayers _ _).mp (p.property α) i h
    exact hleft.trans hright.symm
end Map
end Hindman168.OriginalSameStepLinearization.Realization

namespace Hindman168.OriginalSameStepLinearization
open OAI.Erdos3
variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
abbrev RealAdaptedGroup (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  (F.adaptedPolynomialFiltration w).realification.Group
end Hindman168.OriginalSameStepLinearization
