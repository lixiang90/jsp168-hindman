import Hindman168.AlignedCellDisintegration

namespace Hindman168
open scoped BigOperators

theorem alignedInterval_harmonic_shortCube_gowers_bound
    (X W M a n d J : ℕ) (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (hZ : 0 < harmonicNormalizer X W) (ha : 0 < a) (hn : 0 < n) [NeZero (a * n)]
    [Fintype (multipleAddSubgroup (ZMod (a * n)) a)] (hJ : 0 < J) (hL : 0 < n / J)
    (l u : ℤ) (hlo : (X : ℤ) ≤ l * (M * (a * n) : ℕ))
    (hhi : u * (M * (a * n) : ℕ) ≤ (X ^ 2 : ℕ))
    (hpos : 0 < ∑ y ∈ Finset.Ico (l * (M * (a * n) : ℕ)) (u * (M * (a * n) : ℕ)), integerMass X W y)
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    let R := M * (a * n)
    let I := Finset.Ico (l * R) (u * R)
    let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
    let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
      (∑ y ∈ I, integerMass X W y)
    let t := fun y => finiteHaarMean (fun v₀ : Fin d → Fin (n / J) =>
      finiteHaarMean (fun v₁ : Fin d → Fin (n / J) =>
        ∏ ω : Finset (Fin d), f (y + M * ((a : ℤ) * ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val)))))
    |(∑ y ∈ I, integerMass X W y * t y) / (∑ y ∈ I, integerMass X W y)| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (a * n)) a)
        p (2 ^ d) (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) +
      4 * (d : ℝ) / J + (R : ℝ) / X := by
  classical
  intro R I C p t
  have hk (c : C) : c.val.1 ∈ Finset.Ico l u := (Finset.mem_product.mp c.property).1
  have hr (c : C) : c.val.2.val.Coprime W := (Finset.mem_filter.mp (Finset.mem_product.mp c.property).2).2
  have hclo (c : C) : (X : ℤ) ≤ c.val.1 * (M * (a * n) : ℕ) :=
    hlo.trans (mul_le_mul_of_nonneg_right (Finset.mem_Ico.mp (hk c)).1 (Int.natCast_nonneg _))
  have hchi (c : C) : c.val.1 * (M * (a * n) : ℕ) + (M * (a * n) : ℕ) ≤ (X ^ 2 : ℕ) := by
    have hc : c.val.1 + 1 ≤ u := by have he := (Finset.mem_Ico.mp (hk c)).2; omega
    have he := (mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg (M * (a * n)))).trans hhi
    simpa only [add_mul, one_mul] using he
  have hp (c : C) : 0 ≤ p c := integerMass_cell_probability_nonneg X W _ _ hpos
  have hs : ∑ c : C, p c = 1 := by
    dsimp only [p]
    rw [Finset.sum_coe_sort C (fun c : ℤ × Fin M => (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) / (∑ y ∈ I, integerMass X W y))]
    dsimp only [C]
    refine (Finset.sum_product (Finset.Ico l u) ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W)) (fun c : ℤ × Fin M => (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) / (∑ y ∈ I, integerMass X W y))).trans ?_
    exact alignedInterval_cell_probability_sum X W M (a * n) hM (Nat.mul_pos ha hn) hWM l u hlo hhi hpos
  have hd : (∑ c : C, p c * ((∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val,
        integerMass X W y * t y) / (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y))) =
      (∑ y ∈ I, integerMass X W y * t y) / (∑ y ∈ I, integerMass X W y) := by
    dsimp only [p]
    rw [Finset.sum_coe_sort C (fun c : ℤ × Fin M => ((∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) / (∑ y ∈ I, integerMass X W y)) * ((∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y * t y) / (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y)))]
    dsimp only [C]
    refine (Finset.sum_product (Finset.Ico l u) ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W)) (fun c : ℤ × Fin M => ((∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) / (∑ y ∈ I, integerMass X W y)) * ((∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y * t y) / (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y)))).trans ?_
    exact alignedInterval_conditional_disintegration X W M (a * n) hX hM (Nat.mul_pos ha hn) hWM hZ l u hlo hhi t
  rw [← hd]
  exact weighted_harmonicCell_shortCube_gowers_bound p hp hs X W M a n d J hX hM hWM hZ ha hn hJ hL
    (fun c => c.val.1) (fun c => c.val.2) hr hclo hchi (fun _ => f) (fun _ => hf)

end Hindman168

