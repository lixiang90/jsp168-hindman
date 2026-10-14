import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Int.ModEq

/-! A finite-valued sequence has one actual constant-pattern subsequence.
The reference value is its actual first selected sample, not an arbitrary
or supplied representative. -/
namespace Hindman168
open Filter

theorem finite_sequence_constant_subsequence {A : Type*} [Finite A] (p : ℕ → A) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, p (f n) = p (f 0) := by
  have h : ∃ᶠ n in atTop, ∃ a : A, p n = a :=
    (Eventually.of_forall (fun n => ⟨p n,rfl⟩)).frequently
  obtain ⟨a,ha⟩ := Filter.frequently_exists.mp h
  obtain ⟨f,hf,hconst⟩ := extraction_of_frequently_atTop ha
  exact ⟨f,hf,fun n => (hconst n).trans (hconst 0).symm⟩

def signedPeriodResidue (M : ℕ) (hM : 0 < M) (b : ℤ) : Fin M :=
  ⟨(b % (M : ℤ)).toNat,by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    have hlo := Int.emod_nonneg b hpos.ne'
    have hhi := Int.emod_lt_of_pos b hpos
    have hc := Int.toNat_of_nonneg hlo
    omega⟩

theorem signed_period_residue_cast (M : ℕ) (hM : 0 < M) (b : ℤ) :
    ((signedPeriodResidue M hM b).val : ℤ) = b % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg b (by exact_mod_cast hM.ne'))

theorem signed_period_residue_modEq (M : ℕ) (hM : 0 < M) (b : ℤ) :
    Int.ModEq (M : ℤ) b ((signedPeriodResidue M hM b).val : ℤ) := by
  rw [signed_period_residue_cast]
  exact (Int.mod_modEq b (M : ℤ)).symm

end Hindman168
