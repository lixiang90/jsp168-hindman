import Hindman168.NativeRationalNonlinearKernelFiltration
import Hindman168.NativeLatticeRationalCoordinates

/-! A TRUE highest nonlinear layer and an ACTUAL rational direction with
F(y)=1 are selected from fixed geometry. Its genuine exponential has a
positive lattice power. This preserves weights for later factorization;
no source factorization or correlation transport is inferred. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_highest_nonlinear_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (F : D.E →L[ℝ] ℝ) (hNonzero : ∃ v : D.E, v ∈ L.layer 2 ∧ F v ≠ 0) :
    ∃ j : ℕ, 2 ≤ j ∧ j ≤ ℓ ∧ (∃ v : D.E, v ∈ L.layer j ∧ F v ≠ 0) ∧
      L.layer (j+1) ≤ F.toLinearMap.ker := by
  let S := (Finset.Icc 2 ℓ).filter (fun j => ∃ v : D.E, v ∈ L.layer j ∧ F v ≠ 0)
  have hS : S.Nonempty := ⟨2,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hdeg⟩,hNonzero⟩⟩
  let j := S.max' hS
  have hjS : j ∈ S := Finset.max'_mem S hS
  obtain ⟨hjRange,hjNonzero⟩ := Finset.mem_filter.mp hjS
  obtain ⟨hj2,hjL⟩ := Finset.mem_Icc.mp hjRange
  refine ⟨j,hj2,hjL,hjNonzero,?_⟩
  intro v hv
  change F v=0
  by_cases hnext : j+1 ≤ ℓ
  · by_contra hFv
    have hn : j+1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hnext⟩,⟨v,hv,hFv⟩⟩
    have hle : j+1 ≤ j := Finset.le_max' S (j+1) hn
    omega
  · have hb := L.antitone (show ℓ+1 ≤ j+1 by omega) hv
    rw [L.terminal,Submodule.mem_bot] at hb
    rw [hb,map_zero]

theorem native_rational_highest_layer_direction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (F : D.E →L[ℝ] ℝ)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (hNonzero : ∃ v : D.E, v ∈ L.layer 2 ∧ F v ≠ 0) :
    ∃ (j : ℕ) (y : D.E) (q : ℕ), 2 ≤ j ∧ j ≤ ℓ ∧ y ∈ L.layer j ∧
      y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧ F y=1 ∧
      L.layer (j+1) ≤ F.toLinearMap.ker ∧ 0 < q ∧
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ := by
  obtain ⟨j,hj2,hjL,⟨v,hv,hFv⟩,hHigher⟩ := native_rational_highest_nonlinear_layer D L hdeg F hNonzero
  have hWitness : ∃ w : D.E, w ∈ L.layer j ∧
      w ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧ F w ≠ 0 := by
    by_contra! hNo
    have hk : L.layer j ≤ F.toLinearMap.ker := by
      rw [← L.rational j]
      apply Submodule.span_le.mpr
      intro w hw
      exact hNo w hw.1 hw.2
    exact hFv (hk hv)
  obtain ⟨w,hw,hRatW,hFw⟩ := hWitness
  obtain ⟨a,ha⟩ := hRat w hRatW
  have ha0 : a ≠ 0 := by
    intro hz
    exact hFw (ha.trans (by rw [hz,Rat.cast_zero]))
  let y := (a⁻¹ : ℚ) • w
  have hy : y ∈ L.layer j := by
    dsimp only [y]
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    exact (L.layer j).smul_mem _ hw
  have hyRat : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ :=
    (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ).smul_mem _ hRatW
  have hFy : F y=1 := by
    dsimp only [y]
    rw [← Rat.cast_smul_eq_qsmul ℝ,map_smul,ha,smul_eq_mul,← Rat.cast_mul,inv_mul_cancel₀ ha0,Rat.cast_one]
  obtain ⟨q,hq,hpow⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (I := D.I) D.Γ y).mp hyRat
  exact ⟨j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow⟩

end Hindman168
