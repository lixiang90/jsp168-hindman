import Hindman168.AlignmentResidueBoxTranslation
import Hindman168.RoughRealBoxCeil

/-! Genuine original residue classes reduce modulo a positive step and their
complex mean is the exact normalized integer quotient-box mean. -/
namespace Hindman168
open scoped Classical
variable {κ : Type*} [Fintype κ]

theorem rough_residue_box_reduce (lo hi v : κ → ℤ) (t : ℤ) :
    alignmentBoxClass lo hi v t = alignmentBoxClass lo hi (fun j => v j%t) t := by
  ext x
  simp only [alignmentBoxClass,Fintype.mem_piFinset,alignmentIntervalClass,Finset.mem_filter,Int.ModEq]
  simp only [Int.emod_emod]

theorem rough_integer_real_box (lo hi : κ → ℤ) :
    roughRealIntegerBox (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) =
      Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j)) := by
  simp only [roughRealIntegerBox,Int.ceil_intCast]

theorem rough_residue_box_normalized_mean (lo hi v : κ → ℤ) (t : ℕ) (ht : 0 < t)
    (f : (κ → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass lo hi v t) f =
      finiteComplexSetMean
        (roughRealIntegerBox
          (fun j => (alignmentRetainedEndpoint (lo j) t (v j%t) : ℝ))
          (fun j => (alignmentRetainedEndpoint (hi j) t (v j%t) : ℝ)))
        (fun y => f (fun j => v j%t+(t : ℤ)*y j)) := by
  rw [rough_residue_box_reduce,rough_integer_real_box]
  exact alignment_residue_box_division_mean lo hi (fun j => v j%t) t (by exact_mod_cast ht) f

omit [Fintype κ] in
theorem rough_residue_box_normalized_geometry (lo hi v : κ → ℤ)
    (t : ℕ) (ht : 0 < t) (Z c C : ℝ)
    (hLen : ∀ j, c*Z ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*Z)
    (hLoc : ∀ j, |(lo j : ℝ)| ≤ C*Z ∧ |(hi j : ℝ)| ≤ C*Z)
    (htc : (t : ℝ) ≤ (c/2)*Z) (htZ : (t : ℝ) ≤ Z) :
    (∀ j, (c/2)*(Z/t) ≤ (alignmentRetainedEndpoint (hi j) t (v j%t) : ℝ)-
      alignmentRetainedEndpoint (lo j) t (v j%t)) ∧
    (∀ j, -(C+1)*(Z/t) ≤ (alignmentRetainedEndpoint (lo j) t (v j%t) : ℝ)) ∧
    (∀ j, (alignmentRetainedEndpoint (hi j) t (v j%t) : ℝ) ≤ (C+1)*(Z/t)) := by
  have htI : (0 : ℤ) < t := by exact_mod_cast ht
  have hMod0 (j : κ) : 0 ≤ v j%(t : ℤ) := Int.emod_nonneg _ htI.ne'
  have hModt (j : κ) : v j%(t : ℤ) < t := Int.emod_lt_of_pos _ htI
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (alignmentRetainedEndpoint_sides (lo j) (hi j) t (v j%t) Z c C htI
      (hLen j).1 (hLen j).2 htc htZ).1
  · intro j
    simpa only [Int.cast_natCast,neg_mul] using (abs_le.mp
      (alignmentRetainedEndpoint_location (lo j) t (v j%t) Z C htI
        (hMod0 j) (hModt j) (hLoc j).1 htZ)).1
  · intro j
    exact (abs_le.mp (alignmentRetainedEndpoint_location (hi j) t (v j%t) Z C htI
      (hMod0 j) (hModt j) (hLoc j).2 htZ)).2

end Hindman168
