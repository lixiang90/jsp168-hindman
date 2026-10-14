import Hindman168.ShortCubeWrapBound
import Hindman168.FiniteHaarDirections

namespace Hindman168

theorem finiteHaarMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteHaarMean (fun x => f x - g x) = finiteHaarMean f - finiteHaarMean g := by
  simp only [finiteHaarMean, Finset.sum_sub_distrib, sub_div]

theorem finiteHaarMean_test_error {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (ε : ℝ) (he : ∀ x, |f x - g x| ≤ ε) :
    |finiteHaarMean f - finiteHaarMean g| ≤ ε := by
  rw [← finiteHaarMean_sub]
  exact finiteHaarMean_abs_le _ ε he

end Hindman168
