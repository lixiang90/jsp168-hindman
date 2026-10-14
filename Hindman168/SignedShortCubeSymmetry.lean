import Hindman168.MasterCommonCellProbability

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem shortCube_average_neg (d L : ℕ) (c y : ℤ) (f : Finset (Fin d) → ℤ → ℝ) :
    finiteHaarMean (fun u : Fin d → Fin L => finiteHaarMean (fun v : Fin d → Fin L =>
      ∏ ω : Finset (Fin d), f ω (y + (-c) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))) =
    finiteHaarMean (fun u : Fin d → Fin L => finiteHaarMean (fun v : Fin d → Fin L =>
      ∏ ω : Finset (Fin d), f ω (y + c * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))) := by
  have he (u v : Fin d → Fin L) (ω : Finset (Fin d)) :
      y + (-c) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) =
        y + c * ∑ j ∈ ω, (((u j).val : ℤ) - (v j).val) := by
    simp only [Finset.sum_sub_distrib]
    ring
  simp_rw [he]
  exact finiteHaarMean_comm _

theorem shortCube_average_natAbs (d L : ℕ) (c y : ℤ) (f : Finset (Fin d) → ℤ → ℝ) :
    finiteHaarMean (fun u : Fin d → Fin L => finiteHaarMean (fun v : Fin d → Fin L =>
      ∏ ω : Finset (Fin d), f ω (y + c * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))) =
    finiteHaarMean (fun u : Fin d → Fin L => finiteHaarMean (fun v : Fin d → Fin L =>
      ∏ ω : Finset (Fin d), f ω (y + (c.natAbs : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))) := by
  rw [Int.natCast_natAbs]
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
  · rw [abs_of_neg (lt_of_not_ge hc)]
    exact (shortCube_average_neg d L c y f).symm

theorem MasterParameterConditions.signed_common_cyclic_shortCube_gowers_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ∈ D) (d J : ℕ) (hJ : 0 < J)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let W := primorial w
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let q := R / M
      letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
      let l := (X : ℤ) / R + 1
      let u := ((X ^ 2 : ℕ) : ℤ) / R
      let I := Finset.Ico (l * R) (u * R)
      let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
      let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
        (∑ y ∈ I, integerMass X W y)
      ∀ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) →
      MvPolynomial.eval (fun i => (x i : ℤ)) pol ≠ 0 →
      let P := (predictionCubeModulus w M pol x).natAbs
      let a := P / M
      let b := R / P
      letI : Fintype (multipleAddSubgroup (ZMod q) a) := Fintype.ofFinite _
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      let t := fun y => finiteHaarMean (fun v₀ : Fin d → Fin (b / J) =>
        finiteHaarMean (fun v₁ : Fin d → Fin (b / J) =>
          ∏ ω : Finset (Fin d), f (y + predictionCubeModulus w M pol x * ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val))))
      |∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y * t y| ≤
        (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod q) a)
          p (2 ^ d) (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) +
        4 * (d : ℝ) / J + ε := by
  classical
  filter_upwards [hF.common_cyclic_shortCube_gowers_eventually gap pivot horder pol hpol d J hJ ε hε] with w hw
  dsimp only
  intro x hx hz f hf
  simp_rw [shortCube_average_natAbs d _ (predictionCubeModulus w (F.modulus w) pol x)]
  exact hw x hx hz f hf

end Hindman168
