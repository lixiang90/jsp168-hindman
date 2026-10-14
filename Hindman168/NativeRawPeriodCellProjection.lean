import Hindman168.NativePeriodCellRecipeSynthesis
import Hindman168.NativeFiniteCellProjection

namespace Hindman168
open FiniteMass Filter NNReal
open scoped BigOperators Topology Classical
universe u v

/-- Raw period correlators from a fixed finite native manifold list imply
the original harmonic projection bound. The actual native stage families
and the final selected good-cell family are constructed in the proof. -/
theorem native_projection_lower_from_raw_period_correlators (s : ℕ) {N : ℕ}
    (F : MasterParameterFamily) (U : Ultrafilter ℕ) (gap : ℕ → Fin N)
    (X W M q : ℕ → ℕ) [∀ w, NeZero (q w)]
    (C : (w : ℕ) → Finset (ℤ × Fin (M w)))
    (h : boundedHilbertFamilies (fun w => FiniteMassL2 (integerMass (X w) (W w))))
    (hf : ∀ w y, |h.val w y| ≤ 1)
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0) (K : ℕ) (hK : 0 < K)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (htotal : Tendsto (fun w => ∑ c : C w,
      ∑ y ∈ intervalResidueSet (c.val.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.val.2.val,
        integerMass (X w) (W w) y) (U : Filter ℕ) (𝓝 1))
    (hscale : Tendsto (fun w => (M w * q w : ℕ) / (X w : ℝ)) (U : Filter ℕ) (𝓝 0))
    (hgeom : ∀ᶠ w in (U : Filter ℕ), 0 < X w ∧ 0 < M w ∧ W w ∣ M w ∧
      0 < harmonicNormalizer (X w) (W w) ∧
      (F.modulus w : ℕ) = M w ∧ F.gap w (gap w).val = M w * q w ∧ ∀ c ∈ C w,
        c.2.val.Coprime (W w) ∧ (X w : ℤ) ≤ c.1 * (M w * q w : ℕ) ∧
          c.1 * (M w * q w : ℕ) + (M w * q w : ℕ) ≤ (X w ^ 2 : ℕ)) :
    let mass := fun w (c : C w) => ∑ y ∈ intervalResidueSet
      (c.val.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.val.2.val,
        integerMass (X w) (W w) y
    let p := fun w (c : C w) => mass w c / ∑ a, mass w a
    let f := fun w (c : C w) (z : ZMod (q w)) =>
      h.val w (c.val.1 * (M w * q w : ℕ) + c.val.2.val + (M w : ℤ) * z.val)
    (∀ᶠ w in (U : Filter ℕ),
      δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) (p w) d (f w)) →
    (∀ᶠ w in (U : Filter ℕ), ∀ c : C w,
      δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f w c) →
      ∃ i, HasNativePeriodCellCorrelator (D i) (M w) (q w) K c.val.1 c.val.2
        (fun y => h.val w y) γ (Lip i)) →
    δ ^ (2 ^ d) / 2 * γ ≤
      ‖(nativeNilHilbertSubspace.{u} s F (fun w => integerMass (X w) (W w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ := by
  intro mass p f hglobal hlocal
  let P := fun w (c : C w) =>
    δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f w c)
  let A : Set ℕ := {w | 0 < M w ∧ (F.modulus w : ℕ) = M w ∧
    F.gap w (gap w).val = M w * q w ∧ ∀ c : C w, P w c →
      ∃ i, HasNativePeriodCellCorrelator (D i) (M w) (q w) K c.val.1 c.val.2
        (fun y => h.val w y) γ (Lip i)}
  have hA : ∀ᶠ w in (U : Filter ℕ), w ∈ A := by
    filter_upwards [hgeom, hlocal] with w hw hl
    exact ⟨hw.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, hl⟩
  have hAG : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧ (F.modulus w : ℕ) = M w ∧
      F.gap w (gap w).val = M w * q w := by
    intro w hw
    exact ⟨hw.1, Nat.pos_of_ne_zero (NeZero.ne (q w)), hw.2.1, hw.2.2.1⟩
  obtain ⟨recipes, hr, hb, hgood⟩ := native_indexed_period_cell_recipe_synthesis
    D Lip F gap M q K hK A hAG C P (fun w y => h.val w y) γ (fun w hw => hw.2.2.2)
  apply native_projection_lower_from_finite_cell_recipes s F U gap X W M q C h hf
    recipes (fun i => ⟨D i, hr i⟩) hb d hd δ γ hδ hγ htotal hscale hgeom hglobal
  filter_upwards [hA] with w hw
  exact hgood w hw

end Hindman168
