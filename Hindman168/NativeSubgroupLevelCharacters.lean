import Hindman168.NativeRationalSubgroupTaylorCoordinates
import Hindman168.RationalLocalFunctionalExtension

/-! Geometric rational LEVEL characters and their genuine ambient rational
extensions. Irrationality quantifies over every such character, including
all nonzero rational multiples. It is a target proposition, not a field
of a filtration or a supplied equidistribution theorem. -/
namespace Hindman168
open Filter Submodule
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSubgroupRationalLevelCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ) : Prop :=
  (∃ z : D.E, z ∈ F.layer j ∧ phi z ≠ 0) ∧
  F.layer (j+1) ≤ phi.ker ∧
  (∀ a b : ℕ, 0 < a → 0 < b → a+b=j → ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
    phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0) ∧
  (∀ v ∈ F.layer j, v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ →
    ∃ q : ℚ, phi v = (q : ℝ))

def NativeSubgroupSequentialIrrational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ ℓ → ∀ phi : D.E →ₗ[ℝ] ℝ,
    NativeSubgroupRationalLevelCharacter D F j phi →
    Tendsto (fun n => (L n)^j * ‖(phi (roughVectorMvEval
      (adaptedTaylorResidual D (p n) j) (fun _ => (j : ℝ))) : UnitAddCircle)‖) atTop atTop

theorem native_subgroup_level_character_rational_extension {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ) (hphi : NativeSubgroupRationalLevelCharacter D F j phi) :
    ∃ psi : D.E →ₗ[ℝ] ℝ, (∀ v ∈ F.layer j, psi v = phi v) ∧
      NativeSubgroupRationalLevelCharacter D F j psi ∧
      ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
        ∃ q : ℚ, psi v = (q : ℝ) := by
  let W := nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  obtain ⟨hne,hNext,hBracket,hRat⟩ := hphi
  obtain ⟨psi,hAgree,hGlobal⟩ := rational_local_functional_extension W
    (nativeLattice_rationalLogSpan_finrank (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := D.E) (I := D.I) D.Γ)
    (F.layer j) (F.rational j) phi hRat
  refine ⟨psi,hAgree,?_,hGlobal⟩
  refine ⟨?_,?_,?_,fun v _ hv => hGlobal v hv⟩
  · obtain ⟨z,hz,hz0⟩ := hne
    exact ⟨z,hz,fun he => hz0 ((hAgree z hz).symm.trans he)⟩
  · intro v hv
    exact (hAgree v (F.antitone (Nat.le_succ j) hv)).trans (hNext hv)
  · intro a b ha hb hab v hv w hw
    have hm : nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F.layer j :=
      hab ▸ F.bracket a b v w hv hw
    exact (hAgree _ hm).trans (hBracket a b ha hb hab v hv w hw)

theorem native_subgroup_taylor_character_values_congr {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (phi psi : D.E →ₗ[ℝ] ℝ) (h : ∀ v ∈ F.layer j, phi v = psi v) :
    phi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) =
      psi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) := by
  have hr := native_rational_subgroup_taylor_residual_properties D F p hp j
  exact h _ (native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 j hr.2)

end Hindman168
