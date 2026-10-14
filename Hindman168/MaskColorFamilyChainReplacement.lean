import Hindman168.MaskColorBlockHilbertFamily
import Hindman168.MaskSubsetModelTelescoping

/-! The same preselected Hilbert family replaces the actual color weights
in every later valid chain, simultaneously for all nonsingleton factors.
There is no new model choice after the chain or common gap is selected. -/

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped Topology Classical

noncomputable def maskChainColorWeight {r N : ℕ} (m : ℕ) (hN : 0 < N)
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r)
    (col : Fin (m+1)) : ℕ → ℤ → ℝ :=
  maskBlockColorWeight m hN (C.tail col)
    ⟨C.pivot col, Finset.mem_range.mp (hC col (by simp [Chain.block]))⟩
    (C.tail_nonempty col)
    (fun _ hx => Finset.mem_range.mpr (C.tails_before_pivots col col _ hx))
    (a col) χ (color col)

theorem maskChainColorWeight_bounds {r N : ℕ} (m : ℕ) (hN : 0 < N)
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r)
    (color : Fin (m+1) → Fin r) :
    ∀ᶠ w in atTop, ∀ col y, 0 ≤ maskChainColorWeight m hN C hC a χ color col w y ∧
      maskChainColorWeight m hN C hC a χ color col w y ≤
        masterPredictionBlockMask (maskGeneratedMaster m gap) (fun _ => C) (fun _ => col) w y := by
  have h (col : Fin (m+1)) := maskBlockColorWeight_bounds m hN (C.tail col)
    ⟨C.pivot col, Finset.mem_range.mp (hC col (by simp [Chain.block]))⟩
    (C.tail_nonempty col)
    (fun _ hx => Finset.mem_range.mpr (C.tails_before_pivots col col _ hx))
    (a col) χ (color col)
  filter_upwards [eventually_all.mpr h] with w hw
  exact hw

theorem mask_color_family_chain_targetCube (ι : Type*) [Fintype ι]
    {r N : ℕ} (m d₀ : ℕ) (hN : 0 < N)
    (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i w)))
    (hf : ∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1)
    (hd : ∀ T : Finset ℕ, ∀ i : Fin N, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m d₀ hN T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (l : Fin N) (hgap : ∀ col, l.val ≤ C.pivot col)
    (htail : ∀ col, C.tail col ⊆ Finset.range l.val)
    (γ : Fin (m+1) → ι) (t : Fin (Fintype.card (LargeColumnSubset m)))
    (J : ℕ) (hJ : 0 < J) :
    Tendsto (fun w => maskEndpointTargetCube (fun _ => l) (fun _ => C) t J w
      (fun y => maskChainColorWeight m hN C hC (fun col => a (γ col)) χ
          (fun col => color (γ col)) (targetRootAnchor (fun _ => l) t) w y -
        (f (C.tail (targetRootAnchor (fun _ => l) t))
          (C.pivot (targetRootAnchor (fun _ => l) t)) (γ (targetRootAnchor (fun _ => l) t))).val w y))
      atTop (𝓝 0) := by
  let col := targetRootAnchor (fun _ => l) t
  let i : Fin N := ⟨C.pivot col, Finset.mem_range.mp (hC col (by simp [Chain.block]))⟩
  have hTi : C.tail col ⊆ Finset.range i.val :=
    fun _ hx => Finset.mem_range.mpr (C.tails_before_pivots col col _ hx)
  let gap : MaskValidBlockGap (C.tail col) i := ⟨l, htail col, hgap col⟩
  exact maskBlock_dual_control_targetCube m d₀ hN (C.tail col) i (C.tail_nonempty col) hTi
    (maskChainColorWeight m hN C hC (fun col => a (γ col)) χ (fun col => color (γ col)) col)
    (fun w y => (f (C.tail col) i.val (γ col)).val w y) (hf _ _ _)
    (maskBlockColorWeight_bounds m hN (C.tail col) i (C.tail_nonempty col) hTi
      (a (γ col)) χ (color (γ col)))
    gap (fun _ => C) t (fun _ => rfl) J hJ
    (hd (C.tail col) i (C.tail_nonempty col) hTi (γ col) gap t.succ J (Nat.succ_le_iff.mpr hJ))

theorem mask_color_family_chain_replacements (ι : Type*) [Fintype ι]
    {r N : ℕ} (m d₀ : ℕ) (hN : 0 < N)
    (a : ι → ℚ) (ha : ∀ γ, 0 < a γ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i w)))
    (hf : ∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1)
    (hd : ∀ T : Finset ℕ, ∀ i : Fin N, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m d₀ hN T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (l : Fin N) (hgap : ∀ col, l.val ≤ C.pivot col)
    (htail : ∀ col, C.tail col ⊆ Finset.range l.val) (γ : Fin (m+1) → ι) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ H : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible (fun _ => l) (fun _ => C) w H b →
      (∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card →
        H U = maskChainColorWeight m hN C hC (fun col => a (γ col)) χ
          (fun col => color (γ col)) (U.val.max' U.property) w) →
      |maskOriginalSubsetCorrelation (fun _ => l) (fun col => a (γ col)) (fun _ => C) w H b -
        maskOriginalSubsetCorrelation (fun _ => l) (fun col => a (γ col)) (fun _ => C) w
          (maskSubsetModelReplacement H (fun col y =>
            (f (C.tail col) (C.pivot col) (γ col)).val w y)) b| ≤ ε := by
  exact maskOriginalSubset_all_model_replacements_uniform (fun _ => l) (fun col => a (γ col))
    (fun col => ha (γ col)) (fun _ => C) (fun _ => hC) 1 (by decide)
    (Eventually.of_forall (fun _ => hgap)) (Eventually.of_forall (fun _ => htail))
    (maskChainColorWeight m hN C hC (fun col => a (γ col)) χ (fun col => color (γ col)))
    (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y)
    (fun col => hf _ _ _) (maskChainColorWeight_bounds m hN C hC (fun _ => l)
      (fun col => a (γ col)) χ (fun col => color (γ col)))
    (fun t => mask_color_family_chain_targetCube ι m d₀ hN a χ color f hf hd C hC l hgap htail γ t
      1 (by decide))

end Hindman168
