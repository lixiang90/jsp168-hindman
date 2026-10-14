import Hindman168.NativeGoodCellAssembly
import Hindman168.NativeGoodCellProjectionLower

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u v

/-- The actual finite-list cell correlators are selected and assembled
before applying the original-law projection bound. No global correlating
family is assumed. The finite-list local existence remains an input. -/
theorem native_projection_lower_from_finite_cell_recipes (s : ℕ) {N : ℕ}
    (F : MasterParameterFamily) (U : Ultrafilter ℕ) (gap : ℕ → Fin N)
    (X W M q : ℕ → ℕ) [∀ w, NeZero (q w)]
    (C : (w : ℕ) → Finset (ℤ × Fin (M w)))
    (h : boundedHilbertFamilies (fun w => FiniteMassL2 (integerMass (X w) (W w))))
    (hf : ∀ w y, |h.val w y| ≤ 1)
    {ι : Type v} [Fintype ι] [Nonempty ι] (recipes : ι → ℕ → ℤ → ℝ)
    (hr : ∀ i, NativePieceRepresented.{u} s F gap (recipes i))
    (hb : ∀ i w y, |recipes i w y| ≤ 1)
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
      ∃ i, γ ≤ finiteHaarMean (fun t : Fin (q w) =>
        h.val w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
          recipes i w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) →
    δ ^ (2 ^ d) / 2 * γ ≤
      ‖(nativeNilHilbertSubspace.{u} s F (fun w => integerMass (X w) (W w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ := by
  intro mass p f hglobal hlocal
  let P := fun w (c : C w) =>
    δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f w c)
  let G := fun w => 0 < X w ∧ 0 < M w ∧ W w ∣ M w ∧
    0 < harmonicNormalizer (X w) (W w) ∧ (F.modulus w : ℕ) = M w ∧
    F.gap w (gap w).val = M w * q w ∧ ∀ c ∈ C w,
      c.2.val.Coprime (W w) ∧ (X w : ℤ) ≤ c.1 * (M w * q w : ℕ) ∧
        c.1 * (M w * q w : ℕ) + (M w * q w : ℕ) ≤ (X w ^ 2 : ℕ)
  let L := fun w => ∀ c : C w, P w c → ∃ i,
    γ ≤ finiteHaarMean (fun t : Fin (q w) =>
      h.val w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
        recipes i w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))
  let A : Set ℕ := {w | G w ∧ L w}
  have hA : ∀ᶠ w in (U : Filter ℕ), w ∈ A := hgeom.and hlocal
  have hAG : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧ (F.modulus w : ℕ) = M w ∧
      F.gap w (gap w).val = M w * q w := by
    intro w hw
    exact ⟨hw.1.2.1, Nat.pos_of_ne_zero (NeZero.ne (q w)), hw.1.2.2.2.2.1,
      hw.1.2.2.2.2.2.1⟩
  obtain ⟨V, hV, hVb, hVgood, hVbad, hVzero, _hVstage⟩ :=
    native_good_cell_family_assembly F gap recipes hr hb M q A hAG C P
      (fun w y => h.val w y) γ (fun w hw => hw.2)
  let v := subprobabilityBoundedFamily (fun w => integerMass (X w) (W w))
    (fun w => integerMass_total_le_one (X w) (W w)) V 1 zero_le_one (fun w y _ => hVb w y)
  apply native_good_cells_projection_lower s F U gap X W M q C h v hV hf hVb
    d hd δ γ hδ hγ htotal hscale
  · filter_upwards [hgeom] with w hw
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.2.2⟩
  · filter_upwards [hA, hglobal] with w hw hg
    exact ⟨hg, hVgood w hw, fun c hc => hVbad w c (fun hp => hc hp.2), hVzero w⟩

end Hindman168
