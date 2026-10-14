import Hindman168.MasterMicrocellGrowth
import Hindman168.AlignmentMicrocellFirst

namespace Hindman168
open Filter
open scoped Topology

noncomputable def alignmentLocalLength {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) : ℕ := Nat.sqrt (F.gap w i.val) / (F.modulus w : ℕ)

theorem alignmentLocalLength_exact {n : ℕ} (F : MasterParameterFamily) (w : ℕ) (i : Fin n) :
    (F.modulus w : ℕ) * alignmentLocalLength F w i =
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := rfl

theorem alignmentLocalLength_eventually_large
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F) (i : Fin n) (C : ℝ) :
    ∀ᶠ w in atTop, C ≤ (alignmentLocalLength F w i : ℝ) := by
  have hh := (master_microcell_growth hF (fun _ => i)).2.eventually_bound
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 0
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right C 1))
  filter_upwards [hh] with w hw
  simp only [pow_zero, mul_one] at hw
  exact (le_max_left C 1).trans hw

theorem alignment_actual_microcell_first_distance {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (p : ℤ)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) :
    |alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) p - p| ≤
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) := by
  have hd : (F.modulus w : ℕ) ∣ alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) :=
    ⟨alignmentLocalLength F w i, rfl⟩
  exact alignmentMicrocellFirst_distance _ _ p (by exact_mod_cast (F.modulus w).pos)
    (by exact_mod_cast Nat.le_of_dvd hR hd)

end Hindman168
