import Hindman168.MaskColorProductCalibration
import Hindman168.SelectedColorBlockCoarseTesting

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical
universe u

/-- Calibration on the actual product law at a selected block.
The same model is represented and approximates the own coarse projection. -/
theorem selected_color_block_product_calibration (ι : Type*) [Fintype ι]
    {r n M : ℕ} (m s : ℕ) (hM : 0 < M)
    (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι → boundedHilbertFamilies (fun w => FiniteMassL2
      (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩)) i w)))
    (hf : ∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1)
    (hd : ∀ T : Finset ℕ, ∀ i : Fin M, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m (s+1) hM T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (T : Finset (Fin n)) (b : Fin n) (γ : ι)
    (hT : (T.image (energyPrincipal e)).Nonempty)
    (hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b)
    (model : boundedHilbertFamilies (fun w => FiniteMassL2
      (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩)) (energyPrincipal e b) w)))
    (hmodel : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hM⟩))
      (masterGapIndex M hM (energyPadding e b)) (fun w y => model.val w y))
    (hm : ∀ w y, 0 ≤ model.val w y)
    (ε : ℝ)
    (happrox : ‖(nativeNilHilbertSubspace.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hM⟩))
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩)) (energyPrincipal e b)) U
        (masterGapIndex M hM (energyPadding e b))).starProjection
        (hilbertFamilyToCompletion _ U (f (T.image (energyPrincipal e)) (energyPrincipal e b) γ)) -
      hilbertFamilyToCompletion _ U model‖ < ε)
    (τ : ℝ) (hτ : 0 < τ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      event (originalBlockProductMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩))
        (T.image (energyPrincipal e)) (energyPrincipal e b) hT
        (fun y hy => Finset.mem_range.mpr (hbefore y hy)) w)
        (fun y => 0 < y ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
          (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * y.toNat) = color γ ∧
          model.val w y ≤ 2*τ) < 3*τ + ε + η := by
  let i : Fin M := ⟨energyPrincipal e b, heM _⟩
  let l := masterGapIndex M hM (energyPadding e b) 0
  have hl : l.val = energyPadding e b := masterGapIndex_val M hM _ 0 (heM _)
  have htail : T.image (energyPrincipal e) ⊆ Finset.range l.val := by
    intro y hy
    rw [hl]
    exact Finset.mem_range.mpr (energyTail_before_padding e _ b
      (Finset.image_subset_image (Finset.subset_univ T)) hbefore y hy)
  have hgap : l.val ≤ i.val := by
    rw [hl]
    exact (energyPadding_lt_principal e b).le
  exact maskColorBlock_product_calibration m s hM (T.image (energyPrincipal e)) i hT
    (fun y hy => Finset.mem_range.mpr (hbefore y hy)) (a γ) χ (color γ) U hU
    (f _ _ γ) model (hf _ _ γ) (hd _ _ _ _ γ) ⟨l, htail, hgap⟩ hmodel hm
    ε happrox τ hτ η hη

end Hindman168
