import Hindman168.NilSequenceUniformTesting

/-! Exact refinement of the existing globally anchored piecewise orbits.
The parent map changes only the interval index and preserves the residue;
the orbit exponent remains the original y/M, including for negative y. -/

namespace Hindman168

def intervalResidueParent (R S : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 / ((S / R : ℕ) : ℤ), p.2)

theorem intervalResidueParent_piece (R S M : ℕ) (hRS : R ∣ S) (y : ℤ) :
    intervalResidueParent R S (intervalResiduePiece R M y) = intervalResiduePiece S M y := by
  have he : (R : ℤ) * ((S / R : ℕ) : ℤ) = (S : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hRS
  simp only [intervalResidueParent, intervalResiduePiece,
    Int.ediv_ediv_of_nonneg (Int.natCast_nonneg R), he]

theorem piecewiseLinearNilsequence_refine {G : Type*} [Group G]
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (w : ℕ) (y : ℤ) :
    piecewiseLinearNilsequence Γ F fine
      (fun w p => obs w (intervalResidueParent (F.gap w (fine w).val) (F.gap w (coarse w).val) p))
      (fun w p => g w (intervalResidueParent (F.gap w (fine w).val) (F.gap w (coarse w).val) p))
      (fun w p => x w (intervalResidueParent (F.gap w (fine w).val) (F.gap w (coarse w).val) p)) w y =
      piecewiseLinearNilsequence Γ F coarse obs g x w y := by
  simp only [piecewiseLinearNilsequence, pieceLinearOrbit, intervalResidueParent_piece _ _ _ (hdiv w)]

theorem masterParameter_gap_dvd_of_le {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w i j : ℕ) (hij : i ≤ j) :
    F.gap w i ∣ F.gap w j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact dvd_rfl
  · exact hF.gap_earlier_dvd w i j hij

end Hindman168
