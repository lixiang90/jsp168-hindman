import Hindman168.WeightedShearVectorProjection
import Hindman168.WeightedShearBoxLaw
import Hindman168.NativeConstantProductPerturbation

/-!
The native logarithmic left-translation map is a genuine weighted polynomial
shear in any filtration-adapted coordinates.  The polynomial is the existing
finite Picard product correction; its coordinate-weight bound is proved here,
rather than assumed or replaced by an ordinary-degree bound.
-/

namespace Hindman168
open scoped Manifold ContDiff
open MvPolynomial Module
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- Coordinate-weighted control of the actual native product-log difference polynomial. -/
theorem weightedShear_native_product_perturbation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (weights : σ → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    {u₀ u₁ du w₀ w₁ dw : RoughVectorMvPolynomial σ D.E} {k l : ℕ}
    (hu₀ : AffineShearWeightedVector weights F u₀ k)
    (hu₁ : AffineShearWeightedVector weights F u₁ k)
    (hw₀ : AffineShearWeightedVector weights F w₀ k)
    (hw₁ : AffineShearWeightedVector weights F w₁ k)
    (hdu : AffineShearWeightedVector weights F du l)
    (hdw : AffineShearWeightedVector weights F dw l) :
    AffineShearWeightedVector weights F
      (nativeProductPerturbationPolynomial D u₀ u₁ du w₀ w₁ dw) l := by
  apply affineShear_rough_parametric_weighted_endpoint
  exact affineShear_rough_parametric_picard_perturbation_weighted F hF _ hB _
    hw₀ hw₁ hu₀ hu₁ hdw hdu _

/-- A constant left multiplier spends one unit of the original Lie filtration. -/
theorem weightedShear_native_left_perturbation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (weights : σ → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    {p : RoughVectorMvPolynomial σ D.E}
    (hp : AffineShearWeightedVector weights F p 0) {v : D.E} (hv : v ∈ F 1) :
    AffineShearWeightedVector weights F (nativeLeftConstantPerturbation D p v) 1 := by
  have hc₁ := weightedShearVector_constant weights F hv
  have hc₀ := affineShear_rough_vector_weighted_mono F hF hc₁ (Nat.zero_le 1)
  have hz₀ : AffineShearWeightedVector weights F ([] : RoughVectorMvPolynomial σ D.E) 0 :=
    fun _ ha => False.elim (List.not_mem_nil ha)
  have hz₁ : AffineShearWeightedVector weights F ([] : RoughVectorMvPolynomial σ D.E) 1 :=
    fun _ ha => False.elim (List.not_mem_nil ha)
  exact weightedShear_native_product_perturbation D weights F hF hB hz₀ hc₀ hp hp hc₁ hz₁

/-- The actual coordinate polynomials of native logarithmic left translation. -/
noncomputable def weightedShearNativeLeftDisplacement {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (b : Basis (Fin n) ℝ D.E) (v : D.E) :
    Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => roughVectorMvProjection (b.coord i)
    (nativeLeftConstantPerturbation D (roughVectorMvFromBasis b (fun j => X j)) v)

theorem weightedShearNativeLeftDisplacement_degree {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (weights i))
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    {v : D.E} (hv : v ∈ F 1) (i : Fin n) :
    weightedShearNativeLeftDisplacement D b v i ∈
      weightedShearDegreeLE weights ((weights i : ℤ)-1) := by
  apply weightedShearVector_projection weights F hF (b.coord i) (weights i) (hcoord i)
  exact weightedShear_native_left_perturbation D weights F hF hB
    (weightedShearVector_basis weights F b hb) hv

/-- The scalar polynomials evaluate to the real native BCH displacement. -/
theorem weightedShearNativeLeftDisplacement_eval {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (b : Basis (Fin n) ℝ D.E) (v : D.E)
    (x : Fin n → ℝ) (i : Fin n) :
    x i + MvPolynomial.eval x (weightedShearNativeLeftDisplacement D b v i) =
      b.equivFun (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (I := D.I) (G := D.G) v *
          nativeLieExponential (I := D.I) (G := D.G) (b.equivFun.symm x))) i := by
  rw [weightedShearNativeLeftDisplacement, roughVectorMvProjection_eval,
    native_left_constant_perturbation_eval, roughNativeProductMvPolynomial_eval,
    rough_vector_constant_eval, weightedShearVector_basis_eval, map_sub]
  change x i + ((b.equivFun _) i-(b.equivFun (b.equivFun.symm x)) i) = _
  rw [LinearEquiv.apply_symm_apply]
  abel

/-- Native left multiplication is represented by a member of the one common shear group. -/
theorem weightedShear_native_left_action {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (weights i))
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    {v : D.E} (hv : v ∈ F 1) :
    ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
      f • x = b.equivFun (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (I := D.I) (G := D.G) v *
          nativeLieExponential (I := D.I) (G := D.G) (b.equivFun.symm x))) := by
  let p := weightedShearNativeLeftDisplacement D b v
  have hp := weightedShearNativeLeftDisplacement_degree D weights F hF hB b hb hcoord hv
  refine ⟨weightedShearOfDisplacements weights p hp, ?_⟩
  intro x
  funext i
  rw [weightedShearOfDisplacements_smul]
  exact weightedShearNativeLeftDisplacement_eval D b v x i

end Hindman168
