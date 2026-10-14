import Hindman168.OriginalCellCorrelationSum
import Hindman168.NativeProjectionCorrelation
import Hindman168.HarmonicSubprobability

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- Good-cell correlations of an actual unit native family imply the
paper's projection lower bound on the original integer harmonic Hilbert law.
Complete-cell mass and period-to-cutoff error retain their original limits.
The existence of this correlating family is an explicit remaining input. -/
theorem native_good_cells_projection_lower (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
    (U : Ultrafilter ℕ) (gap : ℕ → Fin N) (X W M q : ℕ → ℕ) [∀ w, NeZero (q w)]
    (C : (w : ℕ) → Finset (ℤ × Fin (M w)))
    (h v : boundedHilbertFamilies (fun w => FiniteMassL2 (integerMass (X w) (W w))))
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y))
    (hf : ∀ w y, |h.val w y| ≤ 1) (hb : ∀ w y, |v.val w y| ≤ 1)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (htotal : Tendsto (fun w => ∑ c : C w,
      ∑ y ∈ intervalResidueSet (c.val.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.val.2.val,
        integerMass (X w) (W w) y) (U : Filter ℕ) (𝓝 1))
    (hscale : Tendsto (fun w => (M w * q w : ℕ) / (X w : ℝ)) (U : Filter ℕ) (𝓝 0))
    (hgeom : ∀ᶠ w in (U : Filter ℕ), 0 < X w ∧ 0 < M w ∧ W w ∣ M w ∧
      0 < harmonicNormalizer (X w) (W w) ∧ ∀ c ∈ C w,
        c.2.val.Coprime (W w) ∧ (X w : ℤ) ≤ c.1 * (M w * q w : ℕ) ∧
          c.1 * (M w * q w : ℕ) + (M w * q w : ℕ) ≤ (X w ^ 2 : ℕ))
    (hcor : ∀ᶠ w in (U : Filter ℕ),
      let cell := fun c : C w => intervalResidueSet
        (c.val.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.val.2.val
      let mass := fun c : C w => ∑ y ∈ cell c, integerMass (X w) (W w) y
      let p := fun c : C w => mass c / ∑ a, mass a
      let f := fun (c : C w) (z : ZMod (q w)) =>
        h.val w (c.val.1 * (M w * q w : ℕ) + c.val.2.val + (M w : ℤ) * z.val)
      δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) p d f ∧
      (∀ c : C w, δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f c) →
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          h.val w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            v.val w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) ∧
      (∀ c : C w, ¬ δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) d (f c) →
        ∀ t : Fin (q w), v.val w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) = 0) ∧
      (∀ y, y ∉ (C w).biUnion (fun c => intervalResidueSet
        (c.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.2.val) → v.val w y = 0)) :
    δ ^ (2 ^ d) / 2 * γ ≤
      ‖(nativeNilHilbertSubspace.{u} s F (fun w => integerMass (X w) (W w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ := by
  let T := fun w => ∑ c : C w, ∑ y ∈ intervalResidueSet
    (c.val.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.val.2.val, integerMass (X w) (W w) y
  let ρ := fun w => (M w * q w : ℕ) / (X w : ℝ)
  let a := δ ^ (2 ^ d) / 2 * γ
  let err := fun w => a * (1 - T w) + T w * ρ w
  have hT : Tendsto T (U : Filter ℕ) (𝓝 1) := htotal
  have hρ : Tendsto ρ (U : Filter ℕ) (𝓝 0) := hscale
  have hz : Tendsto (fun w => 1 - T w) (U : Filter ℕ) (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hT
  have herr : Tendsto err (U : Filter ℕ) (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hz).add (hT.mul hρ)
  apply nativeHilbert_projection_lower_of_eventual_correlation s F
    (fun w => integerMass (X w) (W w)) U gap (fun w => integerMass_total_le_one (X w) (W w))
    h v hv (fun w y _ => hb w y) a err herr
  have hpos := hT.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hgeom, hcor, hpos] with w hgw hcw htw
  obtain ⟨hX, hM, hWM, hZ, hcell⟩ := hgw
  have hC : (C w).Nonempty := by
    by_contra hn
    have he : T w = 0 := Finset.sum_eq_zero (fun c _ => False.elim (hn ⟨c.val, c.property⟩))
    rw [he] at htw
    exact (lt_irrefl (0 : ℝ)) htw
  obtain ⟨hglobal, hgood, hbad, hzero⟩ := hcw
  have he := complete_cells_original_harmonic_correlation_lower (X w) (W w) (M w) (q w)
    hX hM hWM (C w) hC (fun c hc => (hcell c hc).1) hZ
    (fun c hc => (hcell c hc).2.1) (fun c hc => (hcell c hc).2.2)
    (fun y => h.val w y) (hf w) (fun y => v.val w y) (hb w) d hd δ γ hδ hγ
    hglobal hgood hbad hzero
  have hid : a - err w = T w * (a - ρ w) := by
    dsimp only [err]
    ring
  rw [hid]
  exact he

end Hindman168
