import Hindman168.NativeFiniteRecipeBounds
import Hindman168.PieceNilHilbertSubspace

/-! All native step-bounded representations in the original-law Hilbert
space. The represented image itself is linear, before taking its closure. -/

namespace Hindman168
open FiniteMass Filter
universe u

variable (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
  (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ a, 0 ≤ μ w a)] (U : Ultrafilter ℕ)
  (gap : ℕ → Fin N)

noncomputable def nativeBoundedHilbertRecipes :
    Submodule ℝ (boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) where
  carrier := {x | NativePieceRepresented.{u} s F gap (fun w y => x.val w y)}
  zero_mem' := ⟨trivialNativeNilmanifold s, nativePieceOn_const _ F gap 0⟩
  add_mem' := by
    rintro x y ⟨A, hx⟩ ⟨B, hy⟩
    exact ⟨nativeNilmanifoldProduct A B, nativePieceOn_add A B F gap _ _ hx hy⟩
  smul_mem' := by
    rintro r x ⟨D, hx⟩
    exact ⟨D, nativePieceOn_smul D F gap _ hx r⟩

noncomputable def nativeHilbertRepresentations :
    Submodule ℝ (UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :=
  (nativeBoundedHilbertRecipes.{u} s F μ gap).map (hilbertFamilyCompletionLinearMap _ U)

theorem mem_nativeHilbertRepresentations_iff
    (z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :
    z ∈ nativeHilbertRepresentations.{u} s F μ U gap ↔
      ∃ x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
        NativePieceRepresented.{u} s F gap (fun w y => x.val w y) ∧
        hilbertFamilyToCompletion _ U x = z := Iff.rfl

theorem nativeHilbertRepresentations_realize (hprob : ∀ w, total (μ w) = 1)
    (f : ℕ → ℤ → ℝ) (hf : NativePieceRepresented.{u} s F gap f) :
    ∃ x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
      (∀ w y, x.val w y = f w y) ∧
      hilbertFamilyToCompletion _ U x ∈ nativeHilbertRepresentations.{u} s F μ U gap := by
  obtain ⟨D, hD⟩ := hf
  letI := D.metric
  obtain ⟨B, hB, hb⟩ := boundedPieceNilsequence_uniform_bound D.Γ F gap f hD
  let x := finiteMassBoundedFamily μ hprob f B hB (fun w y _ => hb w y)
  exact ⟨x, fun _ _ => rfl, x, ⟨D, hD⟩, rfl⟩

theorem nativeHilbertRepresentations_refine (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val) :
    nativeHilbertRepresentations.{u} s F μ U coarse ≤ nativeHilbertRepresentations.{u} s F μ U fine := by
  rintro z ⟨x, ⟨D, hx⟩, rfl⟩
  exact ⟨x, ⟨D, nativePieceOn_refine D F fine coarse hdiv _ hx⟩, rfl⟩

noncomputable def nativeNilHilbertSubspace :
    Submodule ℝ (UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :=
  (nativeHilbertRepresentations.{u} s F μ U gap).topologicalClosure

theorem nativeNilHilbertSubspace_eq_closedSpan :
    nativeNilHilbertSubspace.{u} s F μ U gap =
      (Submodule.span ℝ (nativeHilbertRepresentations.{u} s F μ U gap : Set _)).topologicalClosure := by
  rw [Submodule.span_eq]
  rfl

theorem nativeNilHilbertSubspace_refine (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val) :
    nativeNilHilbertSubspace.{u} s F μ U coarse ≤ nativeNilHilbertSubspace.{u} s F μ U fine :=
  Submodule.topologicalClosure_mono (nativeHilbertRepresentations_refine s F μ U fine coarse hdiv)

instance nativeNilHilbertSubspace_hasProjection :
    (nativeNilHilbertSubspace.{u} s F μ U gap).HasOrthogonalProjection := by
  unfold nativeNilHilbertSubspace
  infer_instance

theorem nativeNilHilbertSubspace_energy_identity (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (v : UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :
    ‖(nativeNilHilbertSubspace.{u} s F μ U fine).starProjection v -
      (nativeNilHilbertSubspace.{u} s F μ U coarse).starProjection v‖ ^ 2 =
      ‖(nativeNilHilbertSubspace.{u} s F μ U fine).starProjection v‖ ^ 2 -
      ‖(nativeNilHilbertSubspace.{u} s F μ U coarse).starProjection v‖ ^ 2 :=
  nested_projection_energy_identity _ _ (nativeNilHilbertSubspace_refine s F μ U fine coarse hdiv) v

end Hindman168
