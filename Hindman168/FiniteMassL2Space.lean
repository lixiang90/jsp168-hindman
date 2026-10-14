import Hindman168.FiniteWeightedErrors
import Mathlib.Analysis.InnerProductSpace.Basic

/-! The genuine L2 seminorm for the original finitely supported laws.
Zero-weight coordinates are retained until the later zero-distance quotient.
No counting measure or normalized replacement of the given mass is used. -/

namespace Hindman168
open FiniteMass
open scoped BigOperators

variable {α : Type*}

@[implicit_reducible]
noncomputable def finiteMassInnerCore (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a) :
    PreInnerProductSpace.Core ℝ (α → ℝ) where
  inner f g := expectation μ (fun a => f a * g a)
  conj_inner_symm f g := by
    change expectation μ (fun a => g a * f a) = expectation μ (fun a => f a * g a)
    congr 1
    funext a
    exact mul_comm _ _
  re_inner_nonneg f := expectation_nonneg μ _ hμ (fun a => mul_self_nonneg (f a))
  add_left f g h := by
    change expectation μ (fun a => (f a + g a) * h a) = _
    simp only [add_mul, expectation_add]
  smul_left f g r := by
    change expectation μ (fun a => (r * f a) * g a) = r * expectation μ (fun a => f a * g a)
    simp only [expectation, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

def FiniteMassL2 (_μ : Mass α) : Type _ := α → ℝ

instance finiteMassL2AddGroup (μ : Mass α) : AddCommGroup (FiniteMassL2 μ) :=
  inferInstanceAs (AddCommGroup (α → ℝ))

instance finiteMassL2Module (μ : Mass α) : Module ℝ (FiniteMassL2 μ) :=
  inferInstanceAs (Module ℝ (α → ℝ))

noncomputable instance finiteMassL2SeminormedGroup (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)] :
    SeminormedAddCommGroup (FiniteMassL2 μ) :=
  letI : PreInnerProductSpace.Core ℝ (FiniteMassL2 μ) := finiteMassInnerCore μ hμ.out
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance finiteMassL2InnerProduct (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)] :
    InnerProductSpace ℝ (FiniteMassL2 μ) :=
  InnerProductSpace.ofCore (show PreInnerProductSpace.Core ℝ (FiniteMassL2 μ) from
    finiteMassInnerCore μ hμ.out)

theorem finiteMassL2_inner (μ : Mass α) [Fact (∀ a, 0 ≤ μ a)] (f g : FiniteMassL2 μ) :
    inner ℝ f g = expectation μ (fun a => f a * g a) := rfl

theorem finiteMassL2_norm_sq (μ : Mass α) [Fact (∀ a, 0 ≤ μ a)] (f : FiniteMassL2 μ) :
    ‖f‖ ^ 2 = expectation μ (fun a => (f a) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, finiteMassL2_inner]
  simp only [pow_two]

theorem finiteMassL2_norm_le (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)]
    (hprob : total μ = 1) (f : FiniteMassL2 μ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ a ∈ μ.support, |f a| ≤ B) : ‖f‖ ≤ B := by
  have hs : ‖f‖ ^ 2 ≤ B ^ 2 := by
    rw [finiteMassL2_norm_sq]
    calc
      expectation μ (fun a => f a ^ 2) ≤ ∑ a ∈ μ.support, μ a * B ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_left _ (hμ.out a)
        have hh := (sq_le_sq₀ (abs_nonneg (f a)) hB).mpr (hf a ha)
        simpa only [sq_abs] using hh
      _ = total μ * B ^ 2 := by rw [← Finset.sum_mul]; rfl
      _ = B ^ 2 := by rw [hprob, one_mul]
  nlinarith [norm_nonneg f]

end Hindman168
