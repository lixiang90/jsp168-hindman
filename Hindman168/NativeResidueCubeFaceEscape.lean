import Hindman168.NativeResidueCubeLevelCharacter
import Hindman168.NativeSubgroupHorizontalEscape

/-! The selected ACTUAL cube obstruction has an original Taylor face
value escaping every fixed rational multiple, with the required factorial
denominator. Polynomial coefficient isolation is a separate remaining step. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_face_taylor_escape {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hIrr : NativeSubgroupSequentialIrrational D F L p) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ A : Finset (Fin d), A.card ≤ j ∧
      NativeSubgroupRationalLevelCharacter D F j (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A) ∧
      (∀ k : ℕ, j < k → ∀ B : Finset (Fin d), B.card ≤ k →
        F.layer k ≤ (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi B).ker) ∧
      ∀ q : ℚ, q ≠ 0 → Tendsto (fun m => (L m)^j *
        ‖(((q : ℝ) * (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
          (roughVectorMvEval (adaptedTaylorResidual D (p m) j) (fun _ => (j : ℝ))) /
            ((j-A.card).factorial : ℝ)) : ℝ) : UnitAddCircle)‖) atTop atTop := by
  obtain ⟨j,hj,hjTop,A,hA,hLevel,hTail⟩ :=
    native_residue_cube_horizontal_maximal_level D F ρ hρ d n e chi hChi
  refine ⟨j,hj,hjTop,A,hA,hLevel,hTail,?_⟩
  intro q hq
  let phi := nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
  let r : ℚ := q / ((j-A.card).factorial : ℚ)
  have hr : r ≠ 0 := div_ne_zero hq (by positivity)
  have hs := hIrr j hj hjTop ((r : ℝ) • phi)
    (native_subgroup_level_character_rat_smul D F j phi hLevel r hr)
  have he (v : D.E) : ((r : ℝ) • phi) v =
      (q : ℝ) * (phi v / ((j-A.card).factorial : ℝ)) := by
    change (r : ℝ) * phi v = _
    simp only [r,Rat.cast_div,Rat.cast_natCast]
    ring
  simpa only [he] using hs

end Hindman168
