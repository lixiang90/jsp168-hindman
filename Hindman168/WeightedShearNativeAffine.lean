import Hindman168.WeightedShearNativeTranslation
import Hindman168.LieExponentialHomomorphism

/-! The graded identity gives an actual linear-coordinate shear.  Composition
with the proved native left-translation shear gives the native affine action
`log(c * φ(exp Y))`, retaining the very same constant and automorphism. -/

namespace Hindman168
open MvPolynomial Module
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weightedShearLinearDisplacement {n : ℕ}
    (b : Basis (Fin n) ℝ E) (L : E →ₗ[ℝ] E) : Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => roughVectorMvProjection (b.coord i)
    (roughVectorMvLinearMap (L-LinearMap.id) (roughVectorMvFromBasis b (fun j => X j)))

theorem weightedShearLinearDisplacement_degree {n : ℕ} (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (b : Basis (Fin n) ℝ E)
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    (L : E →ₗ[ℝ] E) (hL : ∀ i, L (b i)-b i ∈ F (weights i+1)) (i : Fin n) :
    weightedShearLinearDisplacement b L i ∈ weightedShearDegreeLE weights ((weights i : ℤ)-1) := by
  classical
  apply weightedShearVector_projection weights F hF (b.coord i) (weights i) (hcoord i)
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha'
  simpa [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X, Finsupp.weight_single] using hL j

theorem weightedShearLinearDisplacement_eval {n : ℕ}
    (b : Basis (Fin n) ℝ E) (L : E →ₗ[ℝ] E) (x : Fin n → ℝ) (i : Fin n) :
    x i+MvPolynomial.eval x (weightedShearLinearDisplacement b L i) =
      b.equivFun (L (b.equivFun.symm x)) i := by
  rw [weightedShearLinearDisplacement, roughVectorMvProjection_eval,
    roughVectorMvLinearMap_eval, weightedShearVector_basis_eval]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  change x i+((b.equivFun _) i-(b.equivFun (b.equivFun.symm x)) i) = _
  rw [LinearEquiv.apply_symm_apply]
  abel

/-- The real graded identity is sufficient to realize the linear part inside the common group. -/
theorem weightedShear_linear_action {n : ℕ} (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (b : Basis (Fin n) ℝ E)
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    (L : E →ₗ[ℝ] E) (hL : ∀ i, L (b i)-b i ∈ F (weights i+1)) :
    ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
      f • x = b.equivFun (L (b.equivFun.symm x)) := by
  have hp := weightedShearLinearDisplacement_degree weights F hF b hcoord L hL
  refine ⟨weightedShearOfDisplacements weights (weightedShearLinearDisplacement b L) hp, ?_⟩
  intro x
  funext i
  rw [weightedShearOfDisplacements_smul]
  exact weightedShearLinearDisplacement_eval b L x i

/-- A fixed native left multiplier composed with a graded-identity linear map is a shear. -/
theorem weightedShear_native_affine_action {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (weights i))
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    {v : D.E} (hv : v ∈ F 1) (L : D.E →ₗ[ℝ] D.E)
    (hL : ∀ i, L (b i)-b i ∈ F (weights i+1)) :
    ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
      f • x = b.equivFun (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (I := D.I) (G := D.G) v *
          nativeLieExponential (I := D.I) (G := D.G) (L (b.equivFun.symm x)))) := by
  obtain ⟨f, hf⟩ := weightedShear_native_left_action D weights F hF hB b hb hcoord hv
  obtain ⟨g, hg⟩ := weightedShear_linear_action weights F hF b hcoord L hL
  refine ⟨f*g, ?_⟩
  intro x
  rw [mul_smul, hg, hf, LinearEquiv.symm_apply_apply]

/-- The homomorphism differential viewed in the native vector model. -/
noncomputable def weightedShearNativeDifferential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (φ : D.G →* D.G) : D.E →L[ℝ] D.E :=
  mfderiv D.I D.I (φ : D.G → D.G) 1

/-- The original native affine logarithmic map is a polynomial shear, with its fixed `c,φ`. -/
theorem weightedShear_native_affine_hom_action {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (weights : Fin n → ℕ)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (weights i))
    (hcoord : ∀ i z, z ∈ F (weights i+1) → b.coord i z = 0)
    (c : D.G) (hc : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) c ∈ F 1)
    (φ : D.G →* D.G) (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hgraded : ∀ i, weightedShearNativeDifferential D φ (b i)-b i ∈ F (weights i+1)) :
    ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
      f • x = b.equivFun (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (c * φ (nativeLieExponential (I := D.I) (G := D.G) (b.equivFun.symm x)))) := by
  obtain ⟨f, hf⟩ := weightedShear_native_affine_action D weights F hF hB b hb hcoord hc
    (weightedShearNativeDifferential D φ).toLinearMap hgraded
  refine ⟨f, ?_⟩
  intro x
  rw [hf, nativeLieExponential_globalLogarithm]
  exact congrArg (fun z : D.G => b.equivFun
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (c*z)))
      (nativeLieExponential_map φ hφ (b.equivFun.symm x)).symm

end Hindman168
