import Hindman168.ConditionedDyadicTupleSupport
import Hindman168.IntegerPredictionShortCubeStatistic

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- The original short-cube average, integrated over the actual good
prime-tuple law, is controlled by the proved Bessel threshold with the
paper order 2*(2^d)-1. All boundary and short-increment costs are explicit. -/
theorem constructedMasterFamily_shortCube_bessel_budget_eventually
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ∈ D)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0) (hpolT : pol ∈ T)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (d J : ℕ) (hJ : 0 < J) (η ξ : ℝ) (hη : 0 < η) (hξ : 0 < ξ) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ w in atTop,
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
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      let h := fun (c : C) (z : ZMod q) => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)
      weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p (2 ^ d + 2 ^ d - 1) h ≤ θ →
        expectation μ (fun x => |integerPredictionShortCubeStatistic w M R X d J pol f x|) <
          (2 * (J : ℝ)) ^ d * η + 4 * (d : ℝ) / J + ξ := by
  let F := constructedMasterFamily N D hD
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  obtain ⟨θ, hθ, hb⟩ := constructedMasterFamily_actual_cell_bessel_eventually D hD pol
    (hD pol hpol) T hT gap pivot horder (2 ^ d) (by positivity) η hη
  have hshort := hF.common_cyclic_shortCube_gowers_eventually gap pivot horder pol hpol d J hJ ξ hξ
  have htotal := constructedMasterFamily_primeGoodSample_tendsto_one N D hD T hT
    (fun w => (gap w).val)
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [hb, hshort, htotal.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with w hw hsx ht
  dsimp only
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
  let μ := conditionMass (dyadicPoolTupleMass
    (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
  intro f hf hglobal
  let h := fun (c : C) (z : ZMod q) => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)
  let v := fun x => weightedSubgroupGowersValue
    (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M)) p (2 ^ d) h
  let z := fun x => |integerPredictionShortCubeStatistic w M R X d J pol f x|
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg _)
  have htμ : total μ = 1 := conditionMass_total _ _ ht
  have hv : expectation μ v < η := hw f hf hglobal
  have hz (x : Fin n → ℕ) (hx : x ∈ μ.support) :
      z x ≤ (2 * (J : ℝ)) ^ d * v x + 4 * (d : ℝ) / J + ξ := by
    obtain ⟨hxp, hgood⟩ := conditioned_dyadic_tuple_support (F.pool w (gap w).val) T x hx
    have hpx := hsx x hxp (hgood.2 pol hpolT) f hf
    have hinst : Fintype.ofFinite (multipleAddSubgroup (ZMod q)
        ((predictionCubeModulus w M pol x).natAbs / M)) =
        (inferInstance : Fintype (multipleAddSubgroup (ZMod q)
          ((predictionCubeModulus w M pol x).natAbs / M))) := Subsingleton.elim _ _
    rw [hinst] at hpx
    dsimp only [z, v, h, integerPredictionShortCubeStatistic]
    exact hpx
  have he := expectation_mono_support μ z
    (fun x => (2 * (J : ℝ)) ^ d * v x + 4 * (d : ℝ) / J + ξ) hμ hz
  have hc : 0 < (2 * (J : ℝ)) ^ d := by positivity
  calc
    _ ≤ (2 * (J : ℝ)) ^ d * expectation μ v + 4 * (d : ℝ) / J + ξ := by
      simpa only [expectation_add, expectation_const_mul, expectation_const, htμ, one_mul] using he
    _ < _ := by linarith [mul_lt_mul_of_pos_left hv hc]

end Hindman168
