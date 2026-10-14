import Hindman168.RoughPartitionScaleThresholds
import Hindman168.RoughResidueScaleGrowth

namespace Hindman168
open Filter

theorem rough_piece_descent_thresholds {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w)
    (hZ : ∀ᶠ w in l, 0 ≤ Z w)
    (N K d : ℕ) (hN : 0 < N) (hK : 0 < K)
    (c B η : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ w in l, 0 < Z w ∧ 1 ≤ Z w/K ∧
      ∀ t : ℕ, 0 < t → (t : ℝ) ≤ 2*S w →
        2*(N : ℝ) ≤ c*Z w ∧ 2*(N : ℝ)*K ≤ c*Z w ∧
        2*(t : ℝ) ≤ c*Z w ∧
        η/2+B*(((N^d*K^d : ℕ) : ℝ)*d*(5*(t : ℝ)/(c*Z w)))+
          2*(η/32+η/32) < η := by
  have hlarge := rough_partition_scale_thresholds hg hS hZ N K d hN hK c B (η/8)
    hc hB (by positivity)
  have hscale := rough_residue_scale_eventually_large hg hS hZ K (by exact_mod_cast hK)
  filter_upwards [hlarge, hscale] with w hw hs
  refine ⟨hw.1, hs.le, ?_⟩
  intro t ht htS
  obtain ⟨hn, hnk, hden, herror⟩ := hw.2 t htS
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hNK : 0 ≤ 2*(N : ℝ)*K := by positivity
  refine ⟨hn, ?_, hden, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left ht1 hNK
    nlinarith
  · linarith

end Hindman168
