import Hindman168.ScalarFractionalBracketFirstAlternative
import Hindman168.NativeRationalDenseFractionalPaperSeparation

/-! Genuine first mixed-frequency alternative APPLIED to SAME actual native
fractional parameters and useful shifts. Every density/interval/circle input
is discharged from the actual useful packet, not assumed as a bracket oracle. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_bracket_first_alternative {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (Z δ B : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
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
        (∀ i, (N : ℝ)*‖(nativeRationalCompactBracketCoefficient D L p χ M i : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
          ∃ (k : NativeRationalFirstLayerIndex D L → ℤ) (r : ℤ), (k ≠ 0 ∨ r ≠ 0) ∧
            (∑ i, (k i).natAbs)+r.natAbs ≤ A ∧
            (N : ℝ)*‖(((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i)+
              (r : ℝ)*nativeRationalCompactBracketAlpha D L p hp χ M : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A,hA,hinv⟩ := scalar_fractional_bracket_first_alternative (NativeRationalFirstLayerIndex D L) Z δ B hδ hδ1 hB
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
