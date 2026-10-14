import Hindman168.FiniteHaarDirections
import Hindman168.FiniteHaarCauchySchwarz
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max

namespace Hindman168
open scoped BigOperators Classical

noncomputable def finiteComplexMean {A : Type*} [Fintype A] (f : A → ℂ) : ℂ :=
  (∑ a, f a) / Fintype.card A

theorem finiteComplexMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℂ) : finiteComplexMean (fun a => f (e a)) = finiteComplexMean f := by
  unfold finiteComplexMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteComplexMean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℂ) :
    finiteComplexMean f = finiteComplexMean (fun a => finiteComplexMean (fun b => f (a, b))) := by
  unfold finiteComplexMean
  rw [← Finset.univ_product_univ, Finset.sum_product, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

theorem finiteComplexMean_norm_le {A : Type*} [Fintype A] (f : A → ℂ) :
    ‖finiteComplexMean f‖ ≤ finiteHaarMean (fun a => ‖f a‖) := by
  unfold finiteComplexMean finiteHaarMean
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg _)

theorem finiteComplexMean_norm_le_of_bound {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) : ‖finiteComplexMean f‖ ≤ B := by
  calc
    _ ≤ finiteHaarMean (fun a => ‖f a‖) := finiteComplexMean_norm_le f
    _ ≤ finiteHaarMean (fun _ : A => B) := finiteHaarMean_mono _ _ hf
    _ = B := finiteHaarMean_const B

/-- A complex finite mean has some actual summand of at least its modulus.
No phase agreement between different summands is assumed. -/
theorem finiteComplexMean_exists_norm_ge {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) : ∃ a, ‖finiteComplexMean f‖ ≤ ‖f a‖ := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun a => ‖f a‖) Finset.univ_nonempty
  exact ⟨a, finiteComplexMean_norm_le_of_bound f ‖f a‖ (fun b => ha b (Finset.mem_univ b))⟩

end Hindman168
