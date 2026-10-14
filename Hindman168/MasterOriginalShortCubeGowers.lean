import Hindman168.MasterPredictionShortCubeGeometry

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem MasterParameterConditions.original_shortCube_gowers_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ∈ D) (d J : ℕ) (hJ : 0 < J)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) →
      MvPolynomial.eval (fun i => (x i : ℤ)) pol ≠ 0 →
      let X := F.cutoff w (pivot w).val
      let W := primorial w
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let P := (predictionCubeModulus w M pol x).natAbs
      let a := P / M
      let b := R / P
      ∃ (ha : 0 < a) (hb : 0 < b),
      letI : NeZero (a * b) := ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
      letI : Fintype (multipleAddSubgroup (ZMod (a * b)) a) := Fintype.ofFinite _
      let l := (X : ℤ) / R + 1
      let u := ((X ^ 2 : ℕ) : ℤ) / R
      let I := Finset.Ico (l * R) (u * R)
      let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
      let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
        (∑ y ∈ I, integerMass X W y)
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      let t := fun y => finiteHaarMean (fun v₀ : Fin d → Fin (b / J) =>
        finiteHaarMean (fun v₁ : Fin d → Fin (b / J) =>
          ∏ ω : Finset (Fin d), f (y + (P : ℤ) * ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val))))
      |∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y * t y| ≤
        (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (a * b)) a)
          p (2 ^ d) (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) +
        4 * (d : ℝ) / J + ε := by
  classical
  have herr := (hF.shortCube_fullWindow_remainder_tendsto gap pivot horder).eventually (gt_mem_nhds hε)
  filter_upwards [hF.prediction_shortCube_geometry gap pol hpol J hJ,
    hF.nil_boundary_raw_geometry pivot, hF.primorial_dvd_modulus,
    hF.aligned_interior_mass_eventually_positive gap pivot horder, herr] with w hg hx hwm hi he
  intro x hxp hz
  dsimp only
  obtain ⟨ha, hb, hlen, hwidth, hcoef⟩ := hg x hxp hz
  refine ⟨ha, hb, ?_⟩
  let X := F.cutoff w (pivot w).val
  let W := primorial w
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let P := (predictionCubeModulus w M pol x).natAbs
  let a := P / M
  let b := R / P
  have hwid : M * (a * b) = R := hwidth
  letI : NeZero (a * b) := ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  letI : Fintype (multipleAddSubgroup (ZMod (a * b)) a) := Fintype.ofFinite _
  intro f hf
  have hZ : 0 < harmonicNormalizer X W :=
    (harmonicNormalizer_boundary_lower hx.1 (primorial_pos w) hx.2.1 hx.2.2).1
  have hX : 0 < X := by dsimp [X]; omega
  have hend := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R (hF.gap_positive w (gap w).val)
  have hl : (X : ℤ) ≤ ((X : ℤ) / R + 1) * (M * (a * b) : ℕ) := by simpa only [hwid] using hend.1
  have hu : (((X ^ 2 : ℕ) : ℤ) / R) * (M * (a * b) : ℕ) ≤ (X ^ 2 : ℕ) := by
    simpa only [hwid] using hend.2.2.2
  have hip : 0 < ∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * (M * (a * b) : ℕ))
      ((((X ^ 2 : ℕ) : ℤ) / R) * (M * (a * b) : ℕ)), integerMass X W y := by
    simpa only [hwid] using hi
  have hbound := fullWindow_harmonic_shortCube_gowers_bound X W M a b d J hX (F.modulus w).pos hwm
    hZ ha hb hJ hlen ((X : ℤ) / R + 1) (((X ^ 2 : ℕ) : ℤ) / R) hl hu hip f hf
  have hshift (z : ℤ) : (M : ℤ) * ((a : ℤ) * z) = (P : ℤ) * z := by
    rw [← mul_assoc, ← Nat.cast_mul]
    exact congrArg (fun m : ℕ => (m : ℤ) * z) hcoef
  dsimp only at hbound
  simp only [hwid] at hbound
  simp_rw [hshift] at hbound
  exact hbound.trans (by dsimp only [X, W, R] at *; linarith)

end Hindman168
