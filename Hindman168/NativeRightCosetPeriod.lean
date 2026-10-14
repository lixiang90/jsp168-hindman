import Hindman168.NativeRightFiniteWords
import Hindman168.FiniteSequenceFreeze

/-! The true finite normal-core quotient transfers to the ORIGINAL
nonnormal lattice cosets. ONE period covers every original signed integer
and every unbounded integer correction sequence. ONE constant-pattern
subsequence selects actual rational representatives from a genuine sample. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_right_words_original_coset_of_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n m : ℕ) (b c : ℤ)
    (h : nativeRightFiniteWord D as n b = nativeRightFiniteWord D as m c) :
    (nativeSequentialFactorsRight D n (b : ℝ) as : D.G ⧸ D.Γ) =
      (nativeSequentialFactorsRight D m (c : ℝ) as : D.G ⧸ D.Γ) := by
  have hCore : (nativeRightIntegerWord D as n b)⁻¹ * nativeRightIntegerWord D as m c ∈
      (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore := QuotientGroup.eq.mp h
  have hGamma := (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore_le hCore
  change ((nativeRightIntegerWord D as n b : nativeRightGeneratorGroup D as) : D.G)⁻¹ *
    (nativeRightIntegerWord D as m c : D.G) ∈ D.Γ at hGamma
  rw [native_right_integer_word_original,native_right_integer_word_original] at hGamma
  exact QuotientGroup.eq.mpr hGamma

theorem native_right_word_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (hRat : ∀ a ∈ as, a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (n : ℕ) (b : ℤ) :
    nativeSequentialFactorsRight D n (b : ℝ) as ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ := by
  have h := native_right_generator_group_rational D as hRat (nativeRightIntegerWord D as n b).property
  rw [native_right_integer_word_original] at h
  exact h

theorem native_right_common_original_coset_period {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (hRat : ∀ a ∈ as, a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, ∀ b c : ℤ, Int.ModEq (M : ℤ) b c →
      (nativeSequentialFactorsRight D n (b : ℝ) as : D.G ⧸ D.Γ) =
        (nativeSequentialFactorsRight D n (c : ℝ) as : D.G ⧸ D.Γ) := by
  letI := native_right_core_quotient_finite D as hRat
  exact ⟨Nat.card (NativeRightCoreQuotient D as),Nat.card_pos,fun n b c h =>
    native_right_words_original_coset_of_eq D as n n b c (native_right_finite_word_period D as n h)⟩

theorem native_right_original_frozen_residue_pattern {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (hRat : ∀ a ∈ as, a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ M : ℕ, ∃ hM : 0 < M, ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ sigma : Fin M → D.G,
      (∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) ∧
      ∀ n : ℕ, ∀ b : ℤ, (nativeSequentialFactorsRight D (f n) (b : ℝ) as : D.G ⧸ D.Γ) =
        (sigma (signedPeriodResidue M hM b) : D.G ⧸ D.Γ) := by
  classical
  letI := native_right_core_quotient_finite D as hRat
  let M := Nat.card (NativeRightCoreQuotient D as)
  have hM : 0 < M := Nat.card_pos
  let pattern (n : ℕ) (r : Fin M) := nativeRightFiniteWord D as n (r.val : ℤ)
  obtain ⟨f,hf,hPattern⟩ := finite_sequence_constant_subsequence pattern
  let sigma (r : Fin M) : D.G := nativeSequentialFactorsRight D (f 0) (r.val : ℝ) as
  refine ⟨M,hM,f,hf,sigma,?_,?_⟩
  · intro r
    simpa only [Int.cast_natCast] using native_right_word_rational D as hRat (f 0) (r.val : ℤ)
  · intro n b
    let r := signedPeriodResidue M hM b
    have hMod := signed_period_residue_modEq M hM b
    have h1 := native_right_finite_word_period D as (f n) hMod
    have h2 : nativeRightFiniteWord D as (f n) (r.val : ℤ) = nativeRightFiniteWord D as (f 0) (r.val : ℤ) :=
      congrFun (hPattern n) r
    have hCoset := native_right_words_original_coset_of_eq D as (f n) (f 0) b (r.val : ℤ) (h1.trans h2)
    simpa only [Int.cast_natCast] using hCoset

end Hindman168
