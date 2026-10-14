import Hindman168.NativeTaylorCorrectionRecovery

/-! Raw finite-factor data and their actual native group products. No
factorization, convergence, periodicity or irrationality is a field. The
admissibility predicate records the rational vector and proved scaled error
bound; integer coefficients remain entirely unbounded. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

structure NativeSequentialBinomialFactor {s : ℕ} (D : NativeNilmanifoldData.{u} s) where
  order : ℕ
  vector : D.E
  realCoefficient : ℕ → ℝ
  integerCoefficient : ℕ → ℤ

def NativeSequentialBinomialFactorAdmissible {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ℓ : ℕ) (L : ℕ → ℝ) (a : NativeSequentialBinomialFactor D) : Prop :=
  1 ≤ a.order ∧ a.order ≤ ℓ ∧
    a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, (L n)^a.order * |a.realCoefficient n| ≤ C

noncomputable def nativeSequentialFactorLeft {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) (n : ℕ) (b : ℝ) : D.G :=
  nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    ((a.realCoefficient n * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial a.order)) • a.vector)

noncomputable def nativeSequentialFactorRight {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) (n : ℕ) (b : ℝ) : D.G :=
  nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (((a.integerCoefficient n : ℝ) * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial a.order)) • a.vector)

noncomputable def nativeSequentialFactorsLeft {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (b : ℝ) : List (NativeSequentialBinomialFactor D) → D.G
  | [] => 1
  | a :: as => nativeSequentialFactorLeft D a n b * nativeSequentialFactorsLeft D n b as

noncomputable def nativeSequentialFactorsRight {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (b : ℝ) : List (NativeSequentialBinomialFactor D) → D.G
  | [] => 1
  | a :: as => nativeSequentialFactorsRight D n b as * nativeSequentialFactorRight D a n b

def nativeSequentialFactorReindex {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) (f : ℕ → ℕ) :
    NativeSequentialBinomialFactor D where
  order := a.order
  vector := a.vector
  realCoefficient := a.realCoefficient ∘ f
  integerCoefficient := a.integerCoefficient ∘ f

theorem native_sequential_factor_reindex_admissible {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ℓ : ℕ) (L : ℕ → ℝ) (a : NativeSequentialBinomialFactor D)
    (h : NativeSequentialBinomialFactorAdmissible D ℓ L a) (f : ℕ → ℕ) :
    NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ f) (nativeSequentialFactorReindex D a f) := by
  obtain ⟨hj,hjTop,hRat,C,hC,hbound⟩ := h
  exact ⟨hj,hjTop,hRat,C,hC,fun n => hbound (f n)⟩

theorem native_sequential_factors_left_reindex {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (f : ℕ → ℕ) (n : ℕ) (b : ℝ) :
    nativeSequentialFactorsLeft D n b (as.map (fun a => nativeSequentialFactorReindex D a f)) =
      nativeSequentialFactorsLeft D (f n) b as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      exact congrArg (fun g : D.G => nativeSequentialFactorLeft D a (f n) b * g) ih

theorem native_sequential_factors_right_reindex {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (f : ℕ → ℕ) (n : ℕ) (b : ℝ) :
    nativeSequentialFactorsRight D n b (as.map (fun a => nativeSequentialFactorReindex D a f)) =
      nativeSequentialFactorsRight D (f n) b as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      exact congrArg (fun g : D.G => g * nativeSequentialFactorRight D a (f n) b) ih

end Hindman168
