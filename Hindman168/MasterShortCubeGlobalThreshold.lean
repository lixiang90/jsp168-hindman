import Hindman168.MasterShortCubeBesselBudget

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- For any required short-cube error, choose one fixed quotient J and
one positive global norm threshold. The actual good-tuple harmonic cube
mean is then small eventually, uniformly over all integer unit inputs. -/
theorem constructedMasterFamily_shortCube_global_threshold
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ∈ D)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0) (hpolT : pol ∈ T)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∃ J : ℕ, 0 < J ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ w in atTop,
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
        expectation μ (fun x => |integerPredictionShortCubeStatistic w M R X d J pol f x|) < ε := by
  obtain ⟨J, hlarge⟩ := exists_nat_gt (16 * ((d : ℝ) + 1) / ε)
  have hJR : (0 : ℝ) < J := (div_pos (by positivity) hε).trans hlarge
  have hJ : 0 < J := by exact_mod_cast hJR
  have hcost : 4 * (d : ℝ) / J < ε / 4 := by
    apply (div_lt_iff₀ hJR).mpr
    have hb := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  have hc : 0 < (2 * (J : ℝ)) ^ d := by positivity
  let η := ε / (4 * (2 * (J : ℝ)) ^ d)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hc)
  have hscale : (2 * (J : ℝ)) ^ d * η = ε / 4 := by
    dsimp only [η]
    field_simp [ne_of_gt hc]
  obtain ⟨θ, hθ, he⟩ := constructedMasterFamily_shortCube_bessel_budget_eventually
    D hD pol hpol T hT hpolT gap pivot horder d J hJ η (ε / 4) hη (by positivity)
  refine ⟨J, hJ, θ, hθ, ?_⟩
  filter_upwards [he] with w hw
  dsimp only
  intro f hf hg
  exact (hw f hf hg).trans (by rw [hscale]; linarith)

end Hindman168
