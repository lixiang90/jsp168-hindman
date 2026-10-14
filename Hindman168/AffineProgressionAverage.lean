import Hindman168.HarmonicAffineRoot
import Hindman168.IntegerResidueLaws
import Hindman168.MaskOriginalInsertionPowers
import Mathlib.Algebra.Group.Units.Equiv

/-! Averaging the unnormalized progression density over a harmonic coordinate.
A unit coefficient permutes residues, including the one-point case k = 1. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def residueClassMass (μ : Mass ℤ) (k : ℕ) [NeZero k] (r : ZMod k) : Mass ℤ :=
  (k : ℝ) • restrictedMass μ (fun y => (y : ZMod k) = r)

theorem integerProgressionMass_eq_residueClass (X W k : ℕ) [NeZero k] (h : ℤ) :
    integerProgressionMass X W k h = residueClassMass (integerMass X W) k (h : ZMod k) := by
  unfold integerProgressionMass residueClassMass
  apply congrArg (fun E : ℤ → Prop => (k : ℝ) • restrictedMass (integerMass X W) E)
  funext y
  apply propext
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]

theorem residueClass_expectation (μ : Mass ℤ) (k : ℕ) [NeZero k] (r : ZMod k) (f : ℤ → ℝ) :
    expectation (residueClassMass μ k r) f =
      expectation μ (fun y => if (y : ZMod k) = r then (k : ℝ) * f y else 0) := by
  rw [residueClassMass, expectation_mass_smul, expectation_restrictedMass,
    ← expectation_const_mul]
  apply congrArg (expectation μ)
  funext y
  split_ifs <;> simp

theorem uniform_residueClass_expectation (μ : Mass ℤ) (k : ℕ) [NeZero k] (f : ℤ → ℝ) :
    expectation (uniformFintypeMass (ZMod k)) (fun r => expectation (residueClassMass μ k r) f) =
      expectation μ f := by
  simp_rw [residueClass_expectation]
  rw [expectation_comm]
  apply congrArg (expectation μ)
  funext y
  rw [expectation_eq_sum _ _ (Finset.subset_univ _)]
  simp only [uniformFintypeMass_apply, ZMod.card]
  simp only [mul_ite, mul_zero]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne k), eq_comm]

theorem residueClass_expectation_bound (μ : Mass ℤ) (k : ℕ) [NeZero k]
    (hμ : ∀ y, 0 ≤ μ y) (ht : total μ = 1) (f : ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ y, |f y| ≤ B) (r : ZMod k) :
    |expectation (residueClassMass μ k r) f| ≤ (k : ℝ) * B := by
  rw [residueClass_expectation]
  apply expectation_probability_support_bound μ hμ ht _ _
  intro y _
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (hf y) (Nat.cast_nonneg k)
  · simpa only [abs_zero] using mul_nonneg (Nat.cast_nonneg k) hB

theorem harmonic_affine_zmod_distance {X W k : ℕ} [NeZero k] (b h : ℤ)
    (hX : 2 ≤ X) (hW : 0 < W) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) (hb : IsUnit (b : ZMod k)) :
    distance ((integerMass X W).mapDomain (fun z => ((b * z + h : ℤ) : ZMod k)))
      (uniformFintypeMass (ZMod k)) ≤ residueError X W k := by
  obtain ⟨u, hu⟩ := hb
  let e : ZMod k ≃ ZMod k := u.mulLeft.trans (Equiv.addRight (h : ZMod k))
  have he (z : ℤ) : e (z : ZMod k) = ((b * z + h : ℤ) : ZMod k) := by
    change (u : ZMod k) * (z : ZMod k) + (h : ZMod k) = _
    rw [hu, Int.cast_add, Int.cast_mul]
  have hm : ((integerMass X W).mapDomain (fun z : ℤ => (z : ZMod k))).mapDomain e =
      (integerMass X W).mapDomain (fun z => ((b * z + h : ℤ) : ZMod k)) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr (fun z _ => he z)
  rw [← hm, ← uniformFintypeMass_equiv e, distance_push_injective e.injective]
  exact harmonic_integer_zmod_distance hX hW hco hlog

theorem harmonic_progression_average_error {X W k : ℕ} [NeZero k]
    (μ : Mass ℤ) (hμ : ∀ y, 0 ≤ μ y) (ht : total μ = 1) (b h : ℤ)
    (hX : 2 ≤ X) (hW : 0 < W) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) (hb : IsUnit (b : ZMod k))
    (f : ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B) :
    |expectation (integerMass X W) (fun z =>
        expectation (residueClassMass μ k ((b * z + h : ℤ) : ZMod k)) f) - expectation μ f| ≤
      (k : ℝ) * B * residueError X W k := by
  let g : ZMod k → ℝ := fun r => expectation (residueClassMass μ k r) f
  have he := expectation_difference_bound
    ((integerMass X W).mapDomain (fun z => ((b * z + h : ℤ) : ZMod k)))
    (uniformFintypeMass (ZMod k)) g ((k : ℝ) * B)
    (residueClass_expectation_bound μ k hμ ht f B hB hf)
  rw [expectation_push, uniform_residueClass_expectation] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (harmonic_affine_zmod_distance b h hX hW hco hlog hb)
    (mul_nonneg (Nat.cast_nonneg k) hB))

end Hindman168
