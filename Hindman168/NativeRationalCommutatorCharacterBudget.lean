import Hindman168.NativeRationalIntegralCommutatorCharacter

/-! One genuine finite-family norm budget BEFORE every raw source and
selected relative character. Invalid relative functionals contribute zero;
proof irrelevance preserves the actual character for every valid witness. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_integral_commutator_character_finite_budget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ χ ∈ C,
      ∀ hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
        (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker,
      ∀ i, ‖nativeRationalIntegralCommutatorCharacter D L χ hχ i‖ ≤ R := by
  let f (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
      (i : NativeRationalFirstLayerIndex D L) : D.E →L[ℝ] ℝ :=
    if hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker then
      nativeRationalIntegralCommutatorCharacter D L χ hχ i else 0
  let R := ∑ χ ∈ C, ∑ i, ‖f χ i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨R,hR,?_⟩
  intro χ hχC hχ i
  have hfirst : ‖f χ i‖ ≤ ∑ j, ‖f χ j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hsecond : (∑ j, ‖f χ j‖) ≤ R :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hχC
  have he : f χ i = nativeRationalIntegralCommutatorCharacter D L χ hχ i := by
    dsimp only [f]
    rw [dif_pos hχ]
  rw [he] at hfirst
  exact hfirst.trans hsecond

end Hindman168
