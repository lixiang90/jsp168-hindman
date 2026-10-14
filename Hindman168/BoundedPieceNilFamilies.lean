import Hindman168.NilPieceRefinement

/-! Actual bounded piecewise orbit families on one fixed quotient, with
one observable bound and one Lipschitz constant for ALL stages and pieces.
No nilpotence or compactness property is asserted for an arbitrary group;
those are supplied when this general representation is used on a nilmanifold. -/

namespace Hindman168
open NNReal

variable {G : Type*} [Group G] (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}

def IsBoundedPieceNilsequence (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (f : ℕ → ℤ → ℝ) : Prop :=
  ∃ (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (B : ℝ) (Lip : ℝ≥0), 0 ≤ B ∧
    (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
    f = piecewiseLinearNilsequence Γ F gap obs g x

theorem boundedPieceNilsequence_uniform_bound (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (f : ℕ → ℤ → ℝ) (hf : IsBoundedPieceNilsequence Γ F gap f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w y, |f w y| ≤ B := by
  obtain ⟨obs, g, x, B, Lip, hB, hb, _, rfl⟩ := hf
  exact ⟨B, hB, piecewiseLinearNilsequence_abs_le Γ F gap obs g x B hb⟩

theorem boundedPieceNilsequence_refine (F : MasterParameterFamily) (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (f : ℕ → ℤ → ℝ) (hf : IsBoundedPieceNilsequence Γ F coarse f) :
    IsBoundedPieceNilsequence Γ F fine f := by
  obtain ⟨obs, g, x, B, Lip, hB, hb, hl, rfl⟩ := hf
  let parent := fun w => intervalResidueParent (F.gap w (fine w).val) (F.gap w (coarse w).val)
  refine ⟨fun w p => obs w (parent w p), fun w p => g w (parent w p),
    fun w p => x w (parent w p), B, Lip, hB, ?_, ?_, ?_⟩
  · exact fun w p z => hb w (parent w p) z
  · exact fun w p => hl w (parent w p)
  · funext w y
    exact (piecewiseLinearNilsequence_refine Γ F fine coarse hdiv obs g x w y).symm

theorem boundedPieceNilsequence_master_refine {n : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (fine coarse : ℕ → Fin N)
    (hle : ∀ w, fine w ≤ coarse w) (f : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F coarse f) : IsBoundedPieceNilsequence Γ F fine f :=
  boundedPieceNilsequence_refine Γ F fine coarse
    (fun w => masterParameter_gap_dvd_of_le hF w _ _ (hle w)) f hf

end Hindman168
