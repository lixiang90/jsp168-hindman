import Hindman168.RoughPieceDescentThresholds
import Hindman168.RoughDenominatorUnits

namespace Hindman168
open Filter

/-- One threshold precedes every original box, rough dyadic step and test.
The requested source length is fixed before choosing this threshold. -/
theorem rough_native_descent_budgets {κ : Type*} [Fintype κ]
    {S Z : ℕ → ℝ} (hg : PowerDominates atTop Z S)
    (hS : ∀ᶠ w in atTop, 1 ≤ S w) (hZ : ∀ᶠ w in atTop, 0 ≤ Z w)
    (Part K Src : ℕ) (hPart : 0 < Part) (hK : 0 < K)
    (c B η : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ w in atTop, Src ≤ w ∧ 0 < Z w ∧ 1 ≤ Z w/K ∧
      ∀ t : ℕ, S w ≤ t → (t : ℝ) < 2*S w → (primorial w).Coprime t →
        0 < t ∧ t.Coprime K ∧ 2*(t : ℝ) ≤ c*Z w ∧
        η/2+B*(((Part ^ Fintype.card κ*K ^ Fintype.card κ : ℕ) : ℝ)*
          Fintype.card κ*(5*(t : ℝ)/(c*Z w)))+2*(η/32+η/32) < η ∧
        ∀ lo hi : κ → ℤ, (∀ j, c*Z w ≤ (hi j : ℝ)-lo j) →
          (∀ j, 2*(Part : ℤ) ≤ hi j-lo j) ∧
          (∀ j, (2*Part*K : ℤ) ≤ hi j-lo j) := by
  have hbudget := rough_piece_descent_thresholds hg hS hZ Part K (Fintype.card κ)
    hPart hK c B η hc hB hη
  filter_upwards [hbudget, hS, eventually_ge_atTop Src, eventually_ge_atTop K]
    with w hw hs hsrc hkw
  refine ⟨hsrc, hw.1, hw.2.1, ?_⟩
  intro t htlo hthi hrough
  have ht1 : (1 : ℝ) ≤ t := hs.trans htlo
  have ht : 0 < t := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht1)
  obtain ⟨hn, hnk, htZ, hgap⟩ := hw.2.2 t ht hthi.le
  refine ⟨ht, (fixed_denominator_coprime_rough hK.ne' hkw hrough).symm,
    htZ, hgap, ?_⟩
  intro lo hi hbox
  constructor
  · intro j
    exact_mod_cast hn.trans (hbox j)
  · intro j
    exact_mod_cast hnk.trans (hbox j)

end Hindman168
