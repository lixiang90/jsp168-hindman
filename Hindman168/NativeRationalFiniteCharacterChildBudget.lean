import Hindman168.NativeRationalCharacterChildBudget

/-! ALL valid characters in the ACTUAL original finite pool share ONE
natural geometry/threshold budget and ONE positive child UNIT signal.
Invalid characters and empty pools are treated explicitly by proved
conditioned finite budgeting; no same-degree inverse is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_finite_character_child_budget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (A δ : ℝ) (S : ℕ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S)
    (C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)) :
    ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ χ ∈ C,
      NativeRationalNonlinearityCharacterGood D L χ → NativeRationalCharacterChildBudget D L k A δ S χ B θ := by
  let I := {χ // χ ∈ C}
  obtain ⟨B,hB,θ,hθ,hUniform⟩ := finite_conditioned_signal_budgets
    (fun i : I => NativeRationalNonlinearityCharacterGood D L i.val)
    (fun i n r => NativeRationalCharacterChildBudget D L k A δ S i.val n r)
    (fun i hi => native_rational_character_child_budget_exists D L hdeg k hk A δ S hA hδ hS i.val hi)
  refine ⟨B,hB,θ,hθ,?_⟩
  intro χ hχ hGood
  obtain ⟨n,hn,hnB,r,_hr,hθr,hData⟩ := hUniform ⟨χ,hχ⟩ hGood
  exact native_rational_character_child_budget_mono D L k A δ S χ n B r θ hn hnB hθr hData

end Hindman168
