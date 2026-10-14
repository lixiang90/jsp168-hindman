import Hindman168.NativeLieAdjointEquiv
import Mathlib.Algebra.Lie.Nilpotent

/-! The actual native adjoint preserves the original native Lie bracket.
Pullback naturality of the vector-field bracket and the genuine inverse
of conjugation's derivative prove this; compatibility is not assumed. -/

namespace Hindman168
open Function Set Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjoint_pullback_invariant (g : G) (v : GroupLieAlgebra I G) :
    mpullback I I (fun x : G => g * x * g⁻¹) (mulInvariantVectorField v) =
      mulInvariantVectorField (I := I) (G := G) (nativeLieAdjoint (I := I) g⁻¹ v) := by
  funext x
  rw [mpullback_apply, nativeLieConjugation_inverse_mfderiv]
  have h := lie_hom_derivative_invariant_field (I := I) (J := I)
    (MulAut.conj g⁻¹).toMonoidHom
    ((nativeLieConjugation_contMDiff (I := I) g⁻¹).mdifferentiable (by norm_num)) v (g * x * g⁻¹)
  have hfun : ((MulAut.conj g⁻¹).toMonoidHom : G → G) = (fun y : G => g⁻¹ * y * g) := by
    funext y
    change g⁻¹ * y * (g⁻¹)⁻¹ = g⁻¹ * y * g
    rw [inv_inv]
  rw [hfun] at h
  have hp : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  convert! h using 1
  have he : (fun y : G => g⁻¹ * y * (g⁻¹)⁻¹) = (fun y : G => g⁻¹ * y * g) := by
    funext y
    rw [inv_inv]
  unfold nativeLieAdjoint
  erw [he]
  congr 1
  exact hp.symm

variable [CompleteSpace E]

 theorem nativeLieAdjoint_lie (g : G) (v w : GroupLieAlgebra I G) :
    nativeLieAdjoint (I := I) g (⁅v, w⁆ : GroupLieAlgebra I G) =
      @Bracket.bracket (GroupLieAlgebra I G) (GroupLieAlgebra I G) _
        (nativeLieAdjoint (I := I) g v) (nativeLieAdjoint (I := I) g w) := by
  have h := mpullback_mlieBracket (I := I) (I' := I)
    (f := fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField v) (mdifferentiableAt_mulInvariantVectorField w)
    (nativeLieConjugation_contMDiff (I := I) g⁻¹).contMDiffAt
    (by rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← mulInvariantVector_mlieBracket v w, nativeLieAdjoint_pullback_invariant,
    nativeLieAdjoint_pullback_invariant, nativeLieAdjoint_pullback_invariant] at h
  simp only [inv_inv, ← GroupLieAlgebra.bracket_def, lie_invariant_field_one] at h
  exact h

 noncomputable def nativeLieAdjointLieEquiv (g : G) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G :=
  { (nativeLieAdjointEquiv (I := I) g).toLinearEquiv with
    map_lie' := fun {v w} => nativeLieAdjoint_lie g v w }

 theorem nativeLieAdjointLieEquiv_apply (g : G) (v : GroupLieAlgebra I G) :
    nativeLieAdjointLieEquiv (I := I) g v = nativeLieAdjoint (I := I) g v := rfl

 theorem nativeLieAdjoint_lowerCentral_map (g : G) (k : ℕ) :
    LieIdeal.map (nativeLieAdjointLieEquiv (I := I) g).toLieHom
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) k) =
        LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) k :=
  LieIdeal.lowerCentralSeries_map_eq k (nativeLieAdjointLieEquiv (I := I) g).surjective

end Hindman168
