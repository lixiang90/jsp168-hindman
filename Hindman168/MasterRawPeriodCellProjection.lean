import Hindman168.NativeRawPeriodCellProjection
import Hindman168.MasterCompleteCellProjectionGeometry

namespace Hindman168
open FiniteMass Filter NNReal
open scoped BigOperators Topology Classical
universe u v

/-- The raw fixed-list complex period inverse conclusion already suffices
on the actual master law: all real recipe synthesis, cell selection,
harmonic transfer and projection steps are proved, not extra inputs. -/
theorem MasterParameterConditions.raw_period_correlator_projection_lower
    {n N : ℕ} {A : Finset ℚ} {polys : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A polys F) (s : ℕ) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (h : boundedHilbertFamilies (fun w =>
      FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
    (hf : ∀ w y, |h.val w y| ≤ 1)
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0) (K : ℕ) (hK : 0 < K)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) :
    let q := fun w => F.gap w (gap w).val / (F.modulus w : ℕ)
    letI : ∀ w, NeZero (q w) := fun w => ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
    let C := fun w => masterCompleteCells F gap pivot w
    let mass := fun w (c : C w) => ∑ y ∈ intervalResidueSet
      (c.val.1 * ((F.modulus w : ℕ) * q w : ℕ)) ((F.modulus w : ℕ) * q w)
      (F.modulus w : ℕ) c.val.2.val, integerMass (F.cutoff w (pivot w).val) (primorial w) y
    let p := fun w (c : C w) => mass w c / ∑ a, mass w a
    let f := fun w (c : C w) (z : ZMod (q w)) =>
      h.val w (c.val.1 * ((F.modulus w : ℕ) * q w : ℕ) + c.val.2.val +
        ((F.modulus w : ℕ) : ℤ) * z.val)
    (∀ᶠ w in (U : Filter ℕ),
      δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) (p w) d (f w)) →
    (∀ᶠ w in (U : Filter ℕ), ∀ c : C w,
      δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f w c) →
      ∃ i, HasNativePeriodCellCorrelator (D i) (F.modulus w : ℕ) (q w) K c.val.1 c.val.2
        (fun y => h.val w y) γ (Lip i)) →
    δ ^ (2 ^ d) / 2 * γ ≤
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ := by
  intro q C mass p f hglobal hlocal
  letI : ∀ w, NeZero (q w) := fun w =>
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  apply native_projection_lower_from_raw_period_correlators s F U gap
    (fun w => F.cutoff w (pivot w).val) primorial (fun w => (F.modulus w : ℕ)) q C
    h hf D Lip K hK d hd δ γ hδ hγ
  · exact (hF.complete_cell_mass_tendsto gap pivot horder).mono_left hU
  · exact (hF.complete_cell_scale_ratio_tendsto gap pivot horder).mono_left hU
  · filter_upwards [hU (hF.complete_cell_projection_geometry gap pivot)] with w hw
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, rfl, hw.2.2.2.2.1, hw.2.2.2.2.2⟩
  · exact hglobal
  · exact hlocal

end Hindman168
