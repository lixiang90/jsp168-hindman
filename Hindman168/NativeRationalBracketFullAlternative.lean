import Hindman168.ScalarFractionalBracketFullAlternative
import Hindman168.NativeRationalDenseFractionalPaperSeparation

/-! GENUINE complete bracket alternative APPLIED to SAME native parameters
and actual useful shifts, with positive natural multiplier OR original
nonzero integer vector. No analytic inverse oracle is used. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_bracket_full_alternative {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (Z δ B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (hp : RoughVectorMvWeightedDegree L.layer p 0)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (M : ℕ)
      (b : NativeRationalFirstLayerIndex D L → ℤ),
      (∀ i, |nativeRationalCompactBracketCoefficient D L p χ M i| ≤ Z) →
      ∀ (N : ℕ), 0 < N → ∀ V : Finset ℕ, δ*(N : ℝ) ≤ V.card →
        (∀ h ∈ V, h < N ∧ (N : ℝ)*‖((scalarFractionalBracket
          (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
          (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
          (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B) →
        (∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
          (N : ℝ)*‖(((r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
          ∃ k : NativeRationalFirstLayerIndex D L → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
            (N : ℝ)*‖((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A,hA,hinv⟩ := scalar_fractional_bracket_full_alternative (NativeRationalFirstLayerIndex D L) Z δ B hZ hδ hδ1 hB
  refine ⟨A,hA,?_⟩
  intro p hp χ M b hζ N hN V hdense hUseful
  have hsub : V ⊆ (Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(scalarFractionalBracket (nativeRationalCompactBracketBeta D L p χ M b)
        (nativeRationalCompactBracketAlpha D L p hp χ M) (nativeRationalCompactBracketCoefficient D L p χ M)
        (nativeRationalCompactBracketFrequency D L p) (h : ℝ) : UnitAddCircle)‖ ≤ B) := by
    intro h hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hUseful h hh).1,(hUseful h hh).2⟩
  have hcount : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(scalarFractionalBracket (nativeRationalCompactBracketBeta D L p χ M b)
        (nativeRationalCompactBracketAlpha D L p hp χ M) (nativeRationalCompactBracketCoefficient D L p χ M)
        (nativeRationalCompactBracketFrequency D L p) (h : ℝ) : UnitAddCircle)‖ ≤ B)).card :=
    hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
  exact hinv _ _ _ _ hζ N hN hcount

end Hindman168
