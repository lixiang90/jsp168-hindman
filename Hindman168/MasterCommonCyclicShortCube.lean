import Hindman168.MasterOriginalShortCubeGowers
import Hindman168.MasterSubgroupCombination

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem cyclic_weighted_gowers_order_congr {ι : Type*} [Fintype ι]
    {q r : ℕ} [NeZero q] [NeZero r] (he : q = r) (a d : ℕ)
    (p : ι → ℝ) (h : ι → ℕ → ℝ) :
    letI : Fintype (multipleAddSubgroup (ZMod q) a) := Fintype.ofFinite _
    letI : Fintype (multipleAddSubgroup (ZMod r) a) := Fintype.ofFinite _
    weightedSubgroupGowersValue (multipleAddSubgroup (ZMod q) a) p d (fun c z => h c z.val) =
      weightedSubgroupGowersValue (multipleAddSubgroup (ZMod r) a) p d (fun c z => h c z.val) := by
  subst r
  rfl

theorem MasterParameterConditions.common_cyclic_order_positive
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w l : ℕ) :
    0 < F.gap w l / (F.modulus w : ℕ) :=
  Nat.div_pos (Nat.le_of_dvd (hF.gap_positive w l) (hF.gap_modulus_dvd w l)) (F.modulus w).pos

theorem MasterParameterConditions.common_cyclic_shortCube_gowers_eventually
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
          ∏ ω : Finset (Fin d), f (y + (P : ℤ) * ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val))))
      |∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y * t y| ≤
        (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod q) a)
          p (2 ^ d) (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) +
        4 * (d : ℝ) / J + ε := by
  classical
  filter_upwards [hF.original_shortCube_gowers_eventually gap pivot horder pol hpol d J hJ ε hε] with w hw
  dsimp only
  intro x hx hz
  obtain ⟨ha, hb, hbound⟩ := hw x hx hz
  have heq := (hF.predictionModulus_cyclic_geometry w (gap w).val pol hpol x hx hz).2.2.2
  letI : NeZero ((predictionCubeModulus w (F.modulus w) pol x).natAbs / (F.modulus w : ℕ) *
      (F.gap w (gap w).val / (predictionCubeModulus w (F.modulus w) pol x).natAbs)) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  letI : NeZero (F.gap w (gap w).val / (F.modulus w : ℕ)) :=
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  intro f hf
  let X := F.cutoff w (pivot w).val
  let W := primorial w
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let l := (X : ℤ) / R + 1
  let u := ((X ^ 2 : ℕ) : ℤ) / R
  let I := Finset.Ico (l * R) (u * R)
  let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
  let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
    (∑ y ∈ I, integerMass X W y)
  have hc := cyclic_weighted_gowers_order_congr heq
    ((predictionCubeModulus w M pol x).natAbs / M) (2 ^ d) p
    (fun c k => f (c.val.1 * R + c.val.2.val + (M : ℤ) * k))
  exact (hbound f hf).trans_eq (congrArg (fun v : ℝ => (2 * (J : ℝ)) ^ d * v + 4 * (d : ℝ) / J + ε) hc.symm)

end Hindman168
