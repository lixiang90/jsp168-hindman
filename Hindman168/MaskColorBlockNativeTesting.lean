import Hindman168.MaskColorFamilyCoarseDualControl
import Hindman168.NativeMetricMaskModelTesting

/-! The preselected actual color dense model is asymptotically orthogonal
to every original step-bounded piecewise native test at every permissible
block gap. Its prescribed metric and all stages of its recipe are retained. -/

namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical
universe u

theorem maskColorBlockDualControl_native_testing {r N : ℕ}
    (m s : ℕ) (hN : 0 < N) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) (model : ℕ → ℤ → ℝ)
    (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hd : MaskColorBlockDualControl m (s+1) hN T i hT hTi a χ c model)
    (l : MaskValidBlockGap T i) (v : ℕ → ℤ → ℝ)
    (hv : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => l.val) v) :
    Tendsto (fun w => expectation
      (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val) (primorial w))
      (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - model w y) * v w y))
      atTop (𝓝 0) := by
  obtain ⟨D, hv⟩ := hv
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨obs, g, x, B, Lip, hB, hb, hl, rfl⟩ := hv
  have he := (maskBlockColorWeight_bounds m hN T i hT hTi a χ c).mono
    (fun w hw y => model_error_abs_bound (hw y) (hm w y))
  have hd₀ (J : ℕ) (hJ : 0 < J) (η : ℝ) (hη : 0 < η) :=
    hd l 0 J (Nat.succ_le_iff.mpr hJ) η hη
  have ht := nativeMetric_original_zeroDual_testing_uniform D
    (maskGeneratedMaster_conditions m (fun _ => ⟨0, hN⟩) ∅ (by simp))
    (fun _ => maskBlockChain T i.val hT hTi) (fun _ => maskBlockChain_block_range T i hT hTi)
    (fun _ => 0) (fun _ => l.val) (Eventually.of_forall (fun _ => l.property.2))
    (Eventually.of_forall (fun _ => l.property.1))
    (fun w y => maskBlockColorWeight m hN T i hT hTi a χ c w y - model w y)
    he hd₀ B hB Lip
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ht ε hε] with w hw
  have h := hw ⟨obs w, g w, x w⟩ ⟨hb w, hl w⟩
  simpa only [Real.dist_eq, sub_zero, piecewiseLinearNilsequence, maskBlockChain] using h

theorem mask_color_family_block_native_testing (ι : Type*) [Fintype ι]
    {r N : ℕ} (m s : ℕ) (hN : 0 < N)
    (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i w)))
    (hf : ∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1)
    (hd : ∀ T : Finset ℕ, ∀ i : Fin N, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m (s+1) hN T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (γ : ι) (l : MaskValidBlockGap T i) (v : ℕ → ℤ → ℝ)
    (hv : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => l.val) v) :
    Tendsto (fun w => expectation
      (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (maskBlockColorWeight m hN T i hT hTi (a γ) χ (color γ) w y -
        (f T i.val γ).val w y) * v w y)) atTop (𝓝 0) := by
  exact maskColorBlockDualControl_native_testing m s hN T i hT hTi (a γ) χ (color γ)
    _ (hf _ _ _) (hd T i hT hTi γ) l v hv

end Hindman168
