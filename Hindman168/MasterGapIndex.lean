import Hindman168.NilPieceRefinement

/-! A total index map into the finite master family, equal to the
original index on its valid range and monotone everywhere. -/
namespace Hindman168

def masterGapIndex (M : ℕ) (hM : 0 < M) (i : ℕ) (_w : ℕ) : Fin M :=
  ⟨min i (M - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

theorem masterGapIndex_val (M : ℕ) (hM : 0 < M) (i w : ℕ) (hi : i < M) :
    (masterGapIndex M hM i w).val = i := by
  exact min_eq_left (by omega)

theorem masterGapIndex_mono (M : ℕ) (hM : 0 < M) (l k w : ℕ) (hlk : l ≤ k) :
    masterGapIndex M hM l w ≤ masterGapIndex M hM k w :=
  min_le_min_right _ hlk

theorem MasterParameterConditions.masterGapIndex_dvd {n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (hM : 0 < M)
    (l k : ℕ) (hlk : l ≤ k) (w : ℕ) :
    F.gap w (masterGapIndex M hM l w).val ∣ F.gap w (masterGapIndex M hM k w).val :=
  masterParameter_gap_dvd_of_le hF w _ _ (masterGapIndex_mono M hM l k w hlk)

end Hindman168
