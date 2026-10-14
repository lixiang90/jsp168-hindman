import Hindman168.NativeRationalCharacterInverseInduction

/-! The ACTUAL original finite character pool receives ONE ORIGINAL
inverse budget from legitimate smaller-nonlinearity IH. All valid branch
characters are covered; invalid members and empty pools assert no geometry. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_finite_character_inverse_induction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S B : ℕ) (θ : ℝ)
    (hB : 0 < B) (hθ : 0 < θ) (hA : 0 ≤ A)
    (C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ))
    (hData : ∀ χ ∈ C, NativeRationalNonlinearityCharacterGood D L χ →
      NativeRationalCharacterChildBudget D L k A δ S χ B θ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ χ ∈ C, NativeRationalNonlinearityCharacterGood D L χ →
      NativeRationalCharacterOriginalBudget D L k A δ S χ B Q := by
  let I := {χ // χ ∈ C}
  have hEach (i : I) : ∃ Q : ℕ, 0 < Q ∧
      (NativeRationalNonlinearityCharacterGood D L i.val →
        NativeRationalCharacterOriginalBudget D L k A δ S i.val B Q) := by
    by_cases hi : NativeRationalNonlinearityCharacterGood D L i.val
    · obtain ⟨Q,hQ,hOrig⟩ := native_rational_character_inverse_induction D L hdeg hIH k A δ S i.val
        B θ hB hθ hA (hData i.val i.property hi)
      exact ⟨Q,hQ,fun _ => hOrig⟩
    · exact ⟨1,by omega,fun h => (hi h).elim⟩
  choose q hq hOrig using hEach
  let Q := 1+∑ i, q i
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hqQ (i : I) : q i ≤ Q :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by dsimp only [Q]; omega)
  refine ⟨Q,hQ,?_⟩
  intro χ hχ hGood
  exact native_rational_character_original_budget_mono D L k A δ S χ B (q ⟨χ,hχ⟩) Q
    (hqQ ⟨χ,hχ⟩) (hOrig ⟨χ,hχ⟩ hGood)

end Hindman168
