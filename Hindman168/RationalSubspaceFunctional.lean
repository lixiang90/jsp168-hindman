import Hindman168.RationalSubspaceScalarExtension

/-! Extension of a rational functional through the proved natural scalar
extension, and rationality of its real kernel. -/

namespace Hindman168
open Set Submodule Module
open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

noncomputable def rationalSubspaceFunctional
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) : E →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ (W →ₗ[ℚ] ℝ) ((Algebra.linearMap ℚ ℝ).comp f))).comp
      (rationalSubspaceScalarExtensionEquiv W hdim hspan).symm.toLinearMap

theorem rationalSubspaceFunctional_apply
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) (w : W) :
    rationalSubspaceFunctional W hdim hspan f w = (f w : ℝ) := by
  have he : (rationalSubspaceScalarExtensionEquiv W hdim hspan).symm (w : E) =
      (1 : ℝ) ⊗ₜ[ℚ] w := by
    apply (rationalSubspaceScalarExtensionEquiv W hdim hspan).injective
    rw [LinearEquiv.apply_symm_apply, rationalSubspaceScalarExtensionEquiv_tmul, one_smul]
  change TensorProduct.AlgebraTensorModule.lift _
    ((rationalSubspaceScalarExtensionEquiv W hdim hspan).symm (w : E)) = _
  rw [he, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp

theorem rationalSubspaceFunctional_ne_zero
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) (hf : f ≠ 0) :
    rationalSubspaceFunctional W hdim hspan f ≠ 0 := by
  intro hz
  apply hf
  ext w
  have he := rationalSubspaceFunctional_apply W hdim hspan f w
  rw [hz, LinearMap.zero_apply] at he
  exact_mod_cast he.symm

theorem rationalSubspaceFunctional_kernel_intersection
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) :
    (rationalSubspaceFunctional W hdim hspan f).ker.restrictScalars ℚ ⊓ W =
      f.ker.map W.subtype := by
  ext v
  constructor
  · intro hv
    refine ⟨⟨v, hv.2⟩, ?_, rfl⟩
    have he := rationalSubspaceFunctional_apply W hdim hspan f ⟨v, hv.2⟩
    have hz : rationalSubspaceFunctional W hdim hspan f v = 0 := hv.1
    rw [hz] at he
    exact_mod_cast he.symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, w.property⟩
    change rationalSubspaceFunctional W hdim hspan f w = 0
    rw [rationalSubspaceFunctional_apply]
    change f w = 0 at hw
    rw [hw, Rat.cast_zero]

theorem rationalSubspaceFunctional_kernel_real_span
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) :
    span ℝ (f.ker.map W.subtype : Set E) =
      (rationalSubspaceFunctional W hdim hspan f).ker := by
  let F := rationalSubspaceFunctional W hdim hspan f
  apply le_antisymm
  · apply span_le.mpr
    rintro v ⟨w, hw, rfl⟩
    change F w = 0
    dsimp only [F]
    rw [rationalSubspaceFunctional_apply]
    change f w = 0 at hw
    rw [hw, Rat.cast_zero]
  · by_cases hf : f = 0
    · subst f
      simpa using (show F.ker ≤ span ℝ (W : Set E) from hspan ▸ le_top)
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hf
    have hw0 : f w ≠ 0 := by simpa using hw
    have hFw : F w ≠ 0 := by
      dsimp only [F]
      rw [rationalSubspaceFunctional_apply]
      exact_mod_cast hw0
    let P : E →ₗ[ℝ] E := LinearMap.id -
      (LinearMap.toSpanSingleton ℝ E (w : E)).comp ((F w)⁻¹ • F)
    have hP (v : E) : P v = v - (F v / F w) • (w : E) := by
      simp [P, div_eq_mul_inv, mul_comm]
    have hmap : (span ℝ (W : Set E)).map P ≤ span ℝ (f.ker.map W.subtype : Set E) := by
      rw [Submodule.map_span]
      apply span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      let z : W := ⟨v, hv⟩
      have hk : z - (f z / f w) • w ∈ f.ker := by
        change f (z - (f z / f w) • w) = 0
        simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hw0, sub_self]
      have hm : ((z - (f z / f w) • w : W) : E) ∈
          f.ker.map W.subtype := ⟨_, hk, rfl⟩
      have he : P v = ((z - (f z / f w) • w : W) : E) := by
        rw [hP]
        change v - (F z / F w) • (w : E) = v - (f z / f w) • (w : E)
        dsimp only [F]
        rw [rationalSubspaceFunctional_apply, rationalSubspaceFunctional_apply,
          ← Rat.cast_div, Rat.cast_smul_eq_qsmul]
      exact he ▸ subset_span hm
    rw [hspan] at hmap
    intro v hv
    apply hmap
    refine ⟨v, trivial, ?_⟩
    rw [hP]
    change F v = 0 at hv
    rw [hv, zero_div, zero_smul, sub_zero]

theorem rationalSubspaceFunctional_kernel_rational
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) :
    span ℝ (((rationalSubspaceFunctional W hdim hspan f).ker.restrictScalars ℚ ⊓ W :
      Submodule ℚ E) : Set E) =
      (rationalSubspaceFunctional W hdim hspan f).ker := by
  rw [rationalSubspaceFunctional_kernel_intersection,
    rationalSubspaceFunctional_kernel_real_span]

theorem rationalSubspaceFunctional_unique
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ)
    (F : E →ₗ[ℝ] ℝ) (hF : ∀ w : W, F w = (f w : ℝ)) :
    F = rationalSubspaceFunctional W hdim hspan f := by
  have he : span ℝ (W : Set E) ≤
      LinearMap.eqLocus F (rationalSubspaceFunctional W hdim hspan f) := by
    apply span_le.mpr
    intro w hw
    exact (hF ⟨w, hw⟩).trans
      (rationalSubspaceFunctional_apply W hdim hspan f ⟨w, hw⟩).symm
  ext v
  exact he (hspan ▸ trivial)

theorem rationalSubspaceFunctional_annihilates_real_span
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ)
    (U : Submodule ℚ W) (hU : U ≤ f.ker) :
    span ℝ (U.map W.subtype : Set E) ≤
      (rationalSubspaceFunctional W hdim hspan f).ker := by
  rw [← rationalSubspaceFunctional_kernel_real_span]
  exact Submodule.span_mono (Submodule.map_mono hU)

theorem rationalSubspaceFunctional_kernel_finrank_lt [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : span ℝ (W : Set E) = ⊤) (f : W →ₗ[ℚ] ℚ) (hf : f ≠ 0) :
    Module.finrank ℝ (rationalSubspaceFunctional W hdim hspan f).ker <
      Module.finrank ℝ E := by
  apply Submodule.finrank_lt
  intro htop
  apply rationalSubspaceFunctional_ne_zero W hdim hspan f hf
  exact LinearMap.ker_eq_top.mp htop

end Hindman168
