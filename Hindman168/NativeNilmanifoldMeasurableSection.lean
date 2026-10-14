import Hindman168.MeasurableTransversalEquivalence
import Hindman168.NativeNilmanifoldQuotientProbability

/-! A genuine relatively compact measurable section for ORIGINAL nonnormal
cosets. It is built from the actual finite-patch transversal. -/

namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_measurable_transversal_exists {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∃ F K : Set D.G, MeasurableSet F ∧ IsCompact K ∧ F ⊆ K ∧
      F.InjOn ((↑) : D.G → D.G ⧸ D.Γ) ∧ ∀ y : D.G ⧸ D.Γ, ∃ x ∈ F, (x : D.G ⧸ D.Γ) = y := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_locallyCompact D
  exact discrete_cocompact_transversal D.Γ

noncomputable def nativeNilmanifoldMeasurableTransversal {s : ℕ} (D : NativeNilmanifoldData.{u} s) : Set D.G :=
  Classical.choose (native_nilmanifold_measurable_transversal_exists D)

theorem native_nilmanifold_measurable_transversal_spec {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    MeasurableSet (nativeNilmanifoldMeasurableTransversal D) ∧
      (∃ K : Set D.G, IsCompact K ∧ nativeNilmanifoldMeasurableTransversal D ⊆ K) ∧
      (nativeNilmanifoldMeasurableTransversal D).InjOn ((↑) : D.G → D.G ⧸ D.Γ) ∧
      ∀ y : D.G ⧸ D.Γ, ∃ x ∈ nativeNilmanifoldMeasurableTransversal D, (x : D.G ⧸ D.Γ) = y := by
  letI : MeasurableSpace D.G := borel D.G
  obtain ⟨K, hF, hK, hFK, hinj, hcover⟩ :=
    Classical.choose_spec (native_nilmanifold_measurable_transversal_exists D)
  exact ⟨hF, ⟨K, hK, hFK⟩, hinj, hcover⟩

noncomputable def nativeNilmanifoldTransversalEquiv {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    (nativeNilmanifoldMeasurableTransversal D) ≃ᵐ (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI := native_nilmanifold_group_polish D
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  have h := native_nilmanifold_measurable_transversal_spec D
  exact measurableTransversalEquiv ((↑) : D.G → D.G ⧸ D.Γ) QuotientGroup.continuous_mk
    (nativeNilmanifoldMeasurableTransversal D) h.1 h.2.2.1 h.2.2.2

noncomputable def nativeNilmanifoldMeasurableSection {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (D.G ⧸ D.Γ) → D.G := by
  letI : MeasurableSpace D.G := borel D.G
  exact fun q => ((nativeNilmanifoldTransversalEquiv D).symm q).val

theorem native_nilmanifold_section_right {s : ℕ} (D : NativeNilmanifoldData.{u} s) (q : D.G ⧸ D.Γ) :
    ((nativeNilmanifoldMeasurableSection D q : D.G) : D.G ⧸ D.Γ) = q := by
  letI : MeasurableSpace D.G := borel D.G
  exact (nativeNilmanifoldTransversalEquiv D).apply_symm_apply q

theorem native_nilmanifold_section_measurable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    Measurable (nativeNilmanifoldMeasurableSection D) := by
  letI : MeasurableSpace D.G := borel D.G
  exact measurable_subtype_coe.comp (nativeNilmanifoldTransversalEquiv D).symm.measurable

theorem native_nilmanifold_section_compact_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    ∃ K : Set D.G, IsCompact K ∧ Set.range (nativeNilmanifoldMeasurableSection D) ⊆ K := by
  letI : MeasurableSpace D.G := borel D.G
  obtain ⟨K, hK, hFK⟩ := (native_nilmanifold_measurable_transversal_spec D).2.1
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hFK ((nativeNilmanifoldTransversalEquiv D).symm q).property

end Hindman168
