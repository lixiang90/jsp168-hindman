import Hindman168.AlignedInteriorMassSplit

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem MasterParameterConditions.aligned_interior_mass_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w =>
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      ∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y) atTop (𝓝 1) := by
  have he := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub (hF.aligned_endpoint_loss_tendsto gap pivot horder)
  simp only [sub_zero] at he
  apply he.congr'
  filter_upwards [hF.nil_boundary_raw_geometry pivot] with w hw
  have hz := (harmonicNormalizer_boundary_lower hw.1 (primorial_pos w) hw.2.1 hw.2.2).1
  have hs := alignedInterior_mass_split (F.cutoff w (pivot w).val) (primorial w)
    (F.gap w (gap w).val) (hF.gap_positive w (gap w).val)
  rw [integerMass_total hz] at hs
  dsimp only
  linarith

theorem MasterParameterConditions.aligned_interior_mass_eventually_positive
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      0 < ∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y :=
  (hF.aligned_interior_mass_tendsto gap pivot horder).eventually (lt_mem_nhds (by norm_num))

end Hindman168

