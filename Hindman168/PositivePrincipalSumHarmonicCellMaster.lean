import Hindman168.PositivePrincipalSumHarmonicCellTransfer
import Hindman168.MasterShortCubeRemainder

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem principal_master_microcell_ratio_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) :
    Tendsto (fun w => (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) /
      F.cutoff w i.val) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _
    (hF.cell_width_cutoff_ratio_tendsto (fun _ => i) (fun _ => i) (Eventually.of_forall (fun _ => le_rfl)))
  exact Eventually.of_forall (fun w => div_le_div_of_nonneg_right
    (by exact_mod_cast alignedSqrtWidth_le (F.gap w i.val) (F.modulus w)) (Nat.cast_nonneg _))

/-- Partial endpoint microcells have vanishing actual global raw mass;
this is the existing cutoff theorem at the empty tail, not a new premise. -/
theorem principal_master_partial_microcell_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentShortCutoffGood F w i ∅ x)) atTop (𝓝 0) :=
  alignment_short_cutoff_failure_tendsto hF i ∅

/-- On all original supported complete cells, uniformly over earlier raw
variables and every event, the uniform local cover gives the required
actual harmonic conditional cover. Its only new bad event is that the
uniform union of successes has probability below 3/(4Q). -/
theorem principal_master_microcell_cover_transfer
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n)
    {V : Type*} [Fintype V] (Q : ℕ) (hQ : 0 < Q) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentShortCutoffGood F w i ∅ x → ∀ P : V → ℤ → Prop,
      (3 / (4 * (Q : ℝ)) ≤ event (uniformIntervalMass 0 (alignmentLocalLength F w i))
        (fun ell => ∃ v, P v (alignmentMicrocellFirst
          (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (x i) +
            (F.modulus w : ℤ)*ell))) →
      1 / (2 * (Q : ℝ)) ≤ ∑ v, event
        (conditionMass (integerMass (F.cutoff w i.val) (primorial w))
          (fun z => principalMicrocellExposure
            (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) z =
            principalMicrocellExposure
            (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (x i))) (P v) := by
  have he := (principal_master_microcell_ratio_tendsto hF i).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1/(4*(Q : ℝ)) by positivity))
  filter_upwards [he, hF.raw_cutoffs_valid, hF.primorial_dvd_modulus,
    alignmentLocalLength_eventually_large hF i 1] with w he hv hWM hlen x hx hcut P hcover
  have hq : 0 < alignmentLocalLength F w i := by exact_mod_cast (show (0 : ℝ) < alignmentLocalLength F w i by linarith)
  let r : Fin (F.modulus w : ℕ) := ⟨x i % (F.modulus w : ℕ), Nat.mod_lt _ (F.modulus w).pos⟩
  have hr : r.val.Coprime (primorial w) :=
    (residue_coprime_iff _ _ _ _ hWM rfl).mp (alignmentGlobalRawMass_support_coprime F w x hx i)
  have hres : (x i : ℤ) % (F.modulus w : ℕ) = r.val := by
    exact_mod_cast (rfl : x i % (F.modulus w : ℕ) = r.val)
  have hb : F.cutoff w i.val ≤
      (x i / alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) *
        alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ∧
      (x i / alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) *
        alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) +
        alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ≤ F.cutoff w i.val ^ 2 := by
    simpa [alignmentShortCutoffGood, alignmentShortBinStart, alignmentShortBinVolume,
      alignmentNaturalBlockProduct] using hcut
  have hh := principal_microcell_uniform_cover_transfer (F.cutoff w i.val) (primorial w)
    (F.modulus w) (alignmentLocalLength F w i) Q (x i) r (hF.cutoff_positive w i.val)
    (F.modulus w).pos hq hQ hWM hr hres (hv i.val (Finset.mem_range.mpr i.isLt)).2.2
    (by rw [alignmentLocalLength_exact]; exact_mod_cast hb.1)
    (by rw [alignmentLocalLength_exact]; exact_mod_cast hb.2) P
    (by rw [alignmentLocalLength_exact]; exact he.le)
    (by simpa only [alignmentLocalLength_exact] using hcover)
  simpa only [alignmentLocalLength_exact] using hh
end Hindman168
