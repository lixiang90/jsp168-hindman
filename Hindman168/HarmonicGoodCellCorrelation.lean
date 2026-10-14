import Hindman168.CompleteResidueCellMassAggregate
import Hindman168.SubgroupGowersWeightedBounds
import Mathlib.Algebra.BigOperators.Field

namespace Hindman168
open scoped BigOperators Classical

/-- The paper's good-cell mass estimate, integrated with the actual
conditional cell probabilities and original harmonic masses. -/
theorem complete_cells_good_gowers_harmonic_correlation {ι : Type*}
    [Fintype ι] [Nonempty ι] (X W M q : ℕ) [NeZero q]
    (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (k : ι → ℤ) (r : ι → Fin M) (hr : ∀ c, (r c).val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : ∀ c, (X : ℤ) ≤ k c * (M * q : ℕ))
    (hhi : ∀ c, k c * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) (d : ℕ) (hd : 0 < d)
    (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (V : ι → ℤ → ℝ) (hV : ∀ c y, |V c y| ≤ 1) :
    let cell := fun c => intervalResidueSet (k c * (M * q : ℕ)) (M * q) M (r c).val
    let mass := fun c => ∑ y ∈ cell c, integerMass X W y
    let p := fun c => mass c / ∑ a, mass a
    let h := fun c (z : ZMod q) => f (k c * (M * q : ℕ) + (r c).val + (M : ℤ) * z.val)
    δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p d h →
    (∀ c, δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c) →
      γ ≤ finiteHaarMean (fun t : Fin q =>
        f (completeResidueCellPoint (k c) M q (r c) t) *
          V c (completeResidueCellPoint (k c) M q (r c) t))) →
    (∀ c, ¬ δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c) →
      ∀ t : Fin q, V c (completeResidueCellPoint (k c) M q (r c) t) = 0) →
    δ ^ (2 ^ d) / 2 * γ - ((M * q : ℕ) / (X : ℝ)) ≤
      (∑ c, ∑ y ∈ cell c, integerMass X W y * (f y * V c y)) / ∑ c, mass c := by
  intro cell mass p h hglobal hgood hbad
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have ha c : (X : ℝ) ≤ (k c : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo c
  have hm c : 0 < mass c := completeResidueCell_integerMass_pos X W (k c) M q hM hq
    hWM (r c) (hr c) hZ (hlo c) (hhi c) (hx.trans_le (ha c))
  have ht : 0 < ∑ c, mass c := Finset.sum_pos (fun c _ => hm c) Finset.univ_nonempty
  have hp c : 0 ≤ p c := div_nonneg (hm c).le ht.le
  have hpsum : ∑ c, p c = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div]
    exact div_self ht.ne'
  have hmass := subgroupGowers_good_cell_mass (⊤ : AddSubgroup (ZMod q)) p hp hpsum d hd
    h (fun _ _ => hf _) δ hδ hglobal
  let av := fun c => finiteHaarMean (fun t : Fin q =>
    f (completeResidueCellPoint (k c) M q (r c) t) *
      V c (completeResidueCellPoint (k c) M q (r c) t))
  have hc (c : ι) :
      γ * (if δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c) then p c else 0) ≤
        p c * av c := by
    by_cases hg : δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c)
    · rw [if_pos hg, mul_comm γ]
      exact mul_le_mul_of_nonneg_left (hgood c hg) (hp c)
    · have hz : av c = 0 := by
        dsimp only [av]
        simp only [hbad c hg, mul_zero, finiteHaarMean, Finset.sum_const_zero, zero_div]
      simp only [if_neg hg, hz, mul_zero, le_refl]
  have hav : γ * (δ ^ (2 ^ d) / 2) ≤ ∑ c, p c * av c := by
    calc
      _ ≤ γ * (∑ c, if δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c)
          then p c else 0) := mul_le_mul_of_nonneg_left hmass hγ
      _ = ∑ c, γ * (if δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c)
          then p c else 0) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun c _ => hc c)
  have hav' : γ * (δ ^ (2 ^ d) / 2) ≤ (∑ c, mass c * av c) / ∑ c, mass c := by
    have he : (∑ c, mass c * av c) / ∑ c, mass c = ∑ c, p c * av c := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [p]
      ring
    rwa [he]
  have hF (c : ι) (y : ℤ) : |f y * V c y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hf y) (hV c y) (abs_nonneg _) zero_le_one).trans_eq (mul_one _)
  have he := completeResidueCells_integerMass_aggregate_error X W M q hX hM hq hWM
    k r hr hZ hlo hhi (fun c y => f y * V c y) hF
  change |(∑ c, ∑ y ∈ cell c, integerMass X W y * (f y * V c y)) -
    ∑ c, mass c * av c| ≤ (∑ c, mass c) * ((M * q : ℕ) / (X : ℝ)) at he
  apply (le_div_iff₀ ht).mpr
  have hlocal := (le_div_iff₀ ht).mp hav'
  have herror := (abs_le.mp he).1
  nlinarith only [hlocal, herror]

end Hindman168
