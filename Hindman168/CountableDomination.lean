import Hindman168.CountableExpectations

/-!
# Actual PMF domination under products and statistics

A pointwise mass bound gives summability and an expectation bound for
nonnegative statistics with a finite comparison expectation. The same
bound survives an arbitrary actual pushforward; finite independent raw
products accumulate one constant to the number of raw factors.
-/

namespace Hindman168.DiscreteProduct

open scoped BigOperators Classical ENNReal

theorem weighted_summable_of_domination {α : Type*} (μ ν : PMF α) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ a, (μ a).toReal ≤ C * (ν a).toReal)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hs : Summable (fun a => (ν a).toReal * f a)) :
    Summable (fun a => (μ a).toReal * f a) := by
  apply (hs.mul_left C).of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (hf a))
  intro a
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound a) (hf a)

theorem expectation_le_of_domination {α : Type*} (μ ν : PMF α) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ a, (μ a).toReal ≤ C * (ν a).toReal)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hs : Summable (fun a => (ν a).toReal * f a)) :
    expectation μ f ≤ C * expectation ν f := by
  have h := Summable.tsum_le_tsum
    (fun a => show (μ a).toReal * f a ≤ C * ((ν a).toReal * f a) from
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound a) (hf a))
    (weighted_summable_of_domination μ ν C hC hbound f hf hs) (hs.mul_left C)
  simpa only [expectation, tsum_mul_left] using h

theorem map_atom_domination {α β : Type*} (μ ν : PMF α) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ a, (μ a).toReal ≤ C * (ν a).toReal)
    (stat : α → β) (b : β) :
    ((μ.map stat) b).toReal ≤ C * ((ν.map stat) b).toReal := by
  classical
  have hatom (a : α) : μ a ≤ ENNReal.ofReal C * ν a := by
    have h := ENNReal.ofReal_le_ofReal (hbound a)
    simpa only [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal (μ.apply_ne_top a),
      ENNReal.ofReal_toReal (ν.apply_ne_top a)] using h
  have hmap : (μ.map stat) b ≤ ENNReal.ofReal C * (ν.map stat) b := by
    rw [PMF.map_apply, PMF.map_apply]
    calc
      _ ≤ ∑' a, ENNReal.ofReal C * (if b = stat a then ν a else 0) := by
        apply ENNReal.tsum_le_tsum
        intro a
        split_ifs
        · exact hatom a
        · simp only [mul_zero, le_refl]
      _ = _ := ENNReal.tsum_mul_left
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((ν.map stat).apply_ne_top b)) hmap
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using h

theorem piPMF_atom_domination {ι α : Type*} [Fintype ι] (μ ν : ι → PMF α)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ i a, (μ i a).toReal ≤ C * (ν i a).toReal)
    (x : ι → α) :
    (piPMF μ x).toReal ≤ C ^ Fintype.card ι * (piPMF ν x).toReal := by
  simp only [piPMF_apply, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ i, (C * (ν i (x i)).toReal) :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hbound i (x i))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Hindman168.DiscreteProduct
