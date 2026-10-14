import Hindman168.AffineShearAdaptedBasis
import Hindman168.WeightedShearFilteredTransfer

/-! A single filtration-preserving section lifts every downstairs shear to
one common weighted shear group upstairs.  The section is constructed from
the true image filtration and the original projection; it is not a premise. -/
namespace Hindman168
open Module

 theorem affineShear_weighted_section_lifts {E J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup J] [NormedSpace ℝ J] [FiniteDimensional ℝ J]
    {n m : ℕ} (s : ℕ) (w : Fin n → ℕ) (v : Fin m → ℕ) (hv : ∀ i, 0 < v i)
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (hterm : F (s+1) = ⊥)
    (P : E →ₗ[ℝ] J) (hP : Function.Surjective P)
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (hb : ∀ i, b i ∈ F (w i)) (hc : ∀ i, c i ∈ (F (v i)).map P)
    (hbc : ∀ i z, z ∈ F (w i+1) → b.coord i z = 0)
    (hcc : ∀ i z, z ∈ (F (v i+1)).map P → c.coord i z = 0) :
    ∃ R : J →ₗ[ℝ] E, P.comp R = LinearMap.id ∧
      (∀ k z, z ∈ (F k).map P → R z ∈ F k) ∧
      ∀ T : weightedShearGroup (R := ℝ) v,
        ∃ U : weightedShearGroup (R := ℝ) w,
          (∀ x : Fin n → ℝ, U • x = b.equivFun (b.equivFun.symm x +
            R (c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) - P (b.equivFun.symm x)))) ∧
          ∀ x : Fin n → ℝ, c.equivFun (P (b.equivFun.symm (U • x))) =
            T • c.equivFun (P (b.equivFun.symm x)) := by
  obtain ⟨R, hR, hlevels⟩ := affineShear_terminal_filtered_section_exists P hP s F hF hterm
  have hRlevel : ∀ k z, z ∈ (F k).map P → R z ∈ F k := by
    intro k z hz
    exact hlevels k ⟨z, hz, rfl⟩
  refine ⟨R, hR, hRlevel, ?_⟩
  intro T
  obtain ⟨U, hU⟩ := weightedShear_filtered_joint_lift w v hv F (fun k => (F k).map P)
    hF (fun _ _ h => Submodule.map_mono (hF h)) b c hb hc hbc hcc P
    (fun _ z hz => ⟨z, hz, rfl⟩) R hRlevel T
  refine ⟨U, hU, ?_⟩
  intro x
  rw [hU, LinearEquiv.symm_apply_apply, map_add,
    show P (R (c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) - P (b.equivFun.symm x))) =
      c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) - P (b.equivFun.symm x) from
        LinearMap.congr_fun hR _]
  rw [add_sub_cancel, LinearEquiv.apply_symm_apply]

end Hindman168
