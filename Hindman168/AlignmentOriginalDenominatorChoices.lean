import Hindman168.AlignmentOriginalCubeCRTMean

/-! The FULL fixed finite original denominator-residue list. A sampled choice
is represented exactly by its integer remainder, AFTER sampling; the finite
list itself precedes the analytic cutoff. Terminal retained=1 is step d. -/
namespace Hindman168
open scoped Classical

def alignmentDenominatorChoice {κ : Type*} {d : ℕ} (choice : κ → Fin d) : κ → ℤ :=
  fun j => (choice j).val

def alignmentDenominatorRemainder {κ : Type*} (d : ℕ) (hd : 0 < d) (a : κ → ℤ) : κ → Fin d :=
  fun j => ⟨(a j % (d : ℤ)).toNat,by
    have hp : (0 : ℤ) < d := by exact_mod_cast hd
    have hh := Int.emod_lt_of_pos (a j) hp
    rw [←Int.toNat_of_nonneg (Int.emod_nonneg (a j) hp.ne')] at hh
    exact_mod_cast hh⟩

theorem alignment_denominator_choice_remainder {κ : Type*} (d : ℕ) (hd : 0 < d) (a : κ → ℤ) :
    ∀ j, alignmentDenominatorChoice (alignmentDenominatorRemainder d hd a) j=a j % (d : ℤ) := by
  intro j
  exact Int.toNat_of_nonneg (Int.emod_nonneg (a j) (by exact_mod_cast hd.ne'))

theorem alignment_denominator_remainder_class {κ : Type*} (d : ℕ) (hd : 0 < d) (a : κ → ℤ) :
    ∀ j, Int.ModEq d (a j) (alignmentDenominatorChoice (alignmentDenominatorRemainder d hd a) j) := by
  intro j
  rw [alignment_denominator_choice_remainder]
  exact (Int.mod_modEq (a j) d).symm

theorem alignment_terminal_cube_residue_box {κ : Type*} [Fintype κ]
    (M d : ℕ) (Y rho : ℤ) (choice lo hi : Option κ → ℤ) :
    alignmentBoxClass lo hi (alignmentRetainedCubeResidue M d 1 Y rho choice) d=
      alignmentBoxClass lo hi choice d := by
  have hc := alignment_retained_cube_residue_denominator_class M d 1 (by simp) Y rho choice
  exact alignment_box_class_residue_congr lo hi _ choice d hc

end Hindman168
