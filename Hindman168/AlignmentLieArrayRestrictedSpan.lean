import Hindman168.AlignmentGradedLiePolynomialArrays

/-! Layerwise spanning sets generate the entire original graded array
coefficient space. The same restriction is used at every monomial. -/

namespace Hindman168
open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

def alignmentLieArrayRestrictedGenerators (P : L → Prop) :
    Set (MvPolynomial σ R ⊗[R] L) :=
  {z | ∃ (d : σ →₀ ℕ) (x : L),
    x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1) ∧ P x ∧
      z = MvPolynomial.monomial d 1 ⊗ₜ[R] x}

theorem alignmentLieArrayRestrictedGenerators_subset (P : L → Prop) :
    alignmentLieArrayRestrictedGenerators (σ := σ) (R := R) P ⊆
      alignmentLieArrayGenerators σ R L := by
  rintro _ ⟨d, x, hx, _, rfl⟩
  exact ⟨d, x, hx, rfl⟩

theorem alignmentLieArrayRestrictedGenerators_span (P : L → Prop)
    (hP : ∀ j, Submodule.span R {x : L | x ∈ LieModule.lowerCentralSeries R L L j ∧ P x} =
      (LieModule.lowerCentralSeries R L L j).toSubmodule) :
    Submodule.span R (alignmentLieArrayRestrictedGenerators (σ := σ) (R := R) P) =
      alignmentLieArraySpace σ R L := by
  apply le_antisymm
  · exact Submodule.span_mono (alignmentLieArrayRestrictedGenerators_subset P)
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, x, hx, rfl⟩
    have hx' : x ∈ Submodule.span R
        {x : L | x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1) ∧ P x} := by
      rw [hP]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨d, y, hy.1, hy.2, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ r hy

theorem alignmentLiePolynomialArrays_restricted_span (P : L → Prop)
    (hP : ∀ j, Submodule.span R {x : L | x ∈ LieModule.lowerCentralSeries R L L j ∧ P x} =
      (LieModule.lowerCentralSeries R L L j).toSubmodule) :
    Submodule.span R {x : alignmentLiePolynomialArrays σ R L |
      x.val ∈ alignmentLieArrayRestrictedGenerators P} = ⊤ := by
  apply (Submodule.span_val_image_eq_iff (alignmentLieArraySpace σ R L) _).mp
  have he : Subtype.val '' {x : alignmentLiePolynomialArrays σ R L |
      x.val ∈ alignmentLieArrayRestrictedGenerators P} =
      alignmentLieArrayRestrictedGenerators (σ := σ) (R := R) P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span (alignmentLieArrayRestrictedGenerators_subset P hx)⟩,
        hx, rfl⟩
  exact (congrArg (Submodule.span R) he).trans (alignmentLieArrayRestrictedGenerators_span P hP)

end Hindman168
