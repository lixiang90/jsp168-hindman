import Hindman168.AlignmentLieArrayEvaluation

/-! Genuine lower-central coefficient layers in the scalar-extension Lie
algebra. Bracketing by any polynomial coefficient lowers the layer. -/

namespace Hindman168
open scoped TensorProduct

variable (σ R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def alignmentLieTensorLayer (k : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] L) :=
  Submodule.span R {z | ∃ (p : MvPolynomial σ R) (x : L),
    x ∈ LieModule.lowerCentralSeries R L L k ∧ z = p ⊗ₜ[R] x}

variable {σ R L}

theorem alignmentLieTensorLayer_bracket_next (k : ℕ)
    (x : MvPolynomial σ R ⊗[R] L) {y : MvPolynomial σ R ⊗[R] L}
    (hy : y ∈ alignmentLieTensorLayer σ R L k) :
    ⁅x, y⁆ ∈ alignmentLieTensorLayer σ R L (k + 1) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [zero_lie y]
      exact Submodule.zero_mem _
  | tmul p a =>
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨q, b, hb, rfl⟩ := hy
          rw [LieAlgebra.ExtendScalars.bracket_tmul]
          apply Submodule.subset_span
          refine ⟨p * q, ⁅a, b⁆, ?_, rfl⟩
          rw [LieModule.lowerCentralSeries_succ]
          exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) hb
      | zero =>
          rw [lie_zero (p ⊗ₜ[R] a)]
          exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
          rw [lie_add (p ⊗ₜ[R] a) y z]
          exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
          rw [lie_smul r (p ⊗ₜ[R] a) y]
          exact Submodule.smul_mem _ r hy
  | add x z hx hz =>
      rw [add_lie x z y]
      exact Submodule.add_mem _ hx hz

theorem alignmentLieTensorLayer_lowerCentral_le (k : ℕ) :
    (LieModule.lowerCentralSeries R (MvPolynomial σ R ⊗[R] L)
      (MvPolynomial σ R ⊗[R] L) k).toSubmodule ≤ alignmentLieTensorLayer σ R L k := by
  induction k with
  | zero =>
      have h : ∀ x, x ∈ alignmentLieTensorLayer σ R L 0 := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => exact Submodule.zero_mem _
        | tmul p a => exact Submodule.subset_span ⟨p, a, LieSubmodule.mem_top a, rfl⟩
        | add x y hx hy => exact Submodule.add_mem _ hx hy
      exact fun x _ => h x
  | succ k ih =>
      rw [LieModule.lowerCentralSeries_succ,
        LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro x ⟨a, _, b, hb, rfl⟩
      exact alignmentLieTensorLayer_bracket_next k a (ih hb)

theorem alignmentLieTensorLayer_eq_bot {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    alignmentLieTensorLayer σ R L s = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨p, x, hx, rfl⟩
  rw [hs, LieSubmodule.mem_bot] at hx
  rw [hx, TensorProduct.tmul_zero]
  exact Submodule.zero_mem _

theorem alignmentLieTensor_lowerCentral_bot {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    LieModule.lowerCentralSeries R (MvPolynomial σ R ⊗[R] L)
      (MvPolynomial σ R ⊗[R] L) s = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have h := alignmentLieTensorLayer_lowerCentral_le (σ := σ) s hx
  rw [alignmentLieTensorLayer_eq_bot hs] at h
  exact h

end Hindman168
