import Hindman168.BoundedPieceNilFamilies
import Hindman168.FiniteMassUltrafilterHilbert
import Hindman168.NestedProjectionEnergy

/-! Actual original-law Hilbert images of the uniformly bounded piecewise
orbit families on a fixed quotient, their closed spans and nested projections. -/

namespace Hindman168
open FiniteMass Filter

variable {G : Type*} [Group G] (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}
  (F : MasterParameterFamily) (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ a, 0 ≤ μ w a)]
  (U : Ultrafilter ℕ)

def pieceNilHilbertGenerators (gap : ℕ → Fin N) :
    Set (UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :=
  {z | ∃ x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
    IsBoundedPieceNilsequence Γ F gap (fun w y => x.val w y) ∧
    hilbertFamilyToCompletion _ U x = z}

noncomputable def pieceNilHilbertSubspace (gap : ℕ → Fin N) :
    Submodule ℝ (UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :=
  (Submodule.span ℝ (pieceNilHilbertGenerators Γ F μ U gap)).topologicalClosure

theorem pieceNilHilbertGenerators_realize (gap : ℕ → Fin N)
    (hprob : ∀ w, total (μ w) = 1) (f : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F gap f) :
    ∃ x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
      (∀ w y, x.val w y = f w y) ∧
      hilbertFamilyToCompletion _ U x ∈ pieceNilHilbertGenerators Γ F μ U gap := by
  obtain ⟨B, hB, hb⟩ := boundedPieceNilsequence_uniform_bound Γ F gap f hf
  let x := finiteMassBoundedFamily μ hprob f B hB (fun w y _ => hb w y)
  exact ⟨x, fun _ _ => rfl, x, hf, rfl⟩

theorem pieceNilHilbertGenerators_refine (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val) :
    pieceNilHilbertGenerators Γ F μ U coarse ⊆ pieceNilHilbertGenerators Γ F μ U fine := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, boundedPieceNilsequence_refine Γ F fine coarse hdiv _ hx, rfl⟩

theorem pieceNilHilbertSubspace_refine (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val) :
    pieceNilHilbertSubspace Γ F μ U coarse ≤ pieceNilHilbertSubspace Γ F μ U fine :=
  Submodule.topologicalClosure_mono (Submodule.span_mono
    (pieceNilHilbertGenerators_refine Γ F μ U fine coarse hdiv))

instance pieceNilHilbertSubspace_hasProjection (gap : ℕ → Fin N) :
    (pieceNilHilbertSubspace Γ F μ U gap).HasOrthogonalProjection := by
  unfold pieceNilHilbertSubspace
  infer_instance

theorem pieceNilHilbertSubspace_energy_identity (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (v : UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U) :
    ‖(pieceNilHilbertSubspace Γ F μ U fine).starProjection v -
      (pieceNilHilbertSubspace Γ F μ U coarse).starProjection v‖ ^ 2 =
      ‖(pieceNilHilbertSubspace Γ F μ U fine).starProjection v‖ ^ 2 -
      ‖(pieceNilHilbertSubspace Γ F μ U coarse).starProjection v‖ ^ 2 :=
  nested_projection_energy_identity _ _ (pieceNilHilbertSubspace_refine Γ F μ U fine coarse hdiv) v

end Hindman168
