import Hindman168.NativeNilmanifoldFundamentalDomain
import Hindman168.FundamentalCosetProbability

/-! Actual normalized invariant probability on the ORIGINAL nonnormal
native coset space, constructed from the ORIGINAL positive finite Haar domain. -/

namespace Hindman168
open Set MeasureTheory Measure
open scoped Manifold ContDiff
universe u

noncomputable def nativeNilmanifoldQuotientProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  exact fundamentalCosetProbability D.Γ (nativeNilmanifoldGroupHaar D) (nativeNilmanifoldFundamentalDomain D)

theorem native_nilmanifold_quotient_probability_isProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativeNilmanifoldQuotientProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  have h := native_nilmanifold_fundamental_domain_spec D
  exact fundamental_coset_probability_isProbability D.Γ (nativeNilmanifoldGroupHaar D)
    (nativeNilmanifoldFundamentalDomain D) h.2.2.1 h.2.2.2.1

theorem native_nilmanifold_quotient_probability_invariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    SMulInvariantMeasure D.G (D.G ⧸ D.Γ) (nativeNilmanifoldQuotientProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  letI : Countable D.Γ := native_nilmanifold_lattice_countable D
  letI : IsHaarMeasure (nativeNilmanifoldGroupHaar D) := native_nilmanifold_group_haar_isHaar D
  letI : IsMulRightInvariant (nativeNilmanifoldGroupHaar D) := native_nilmanifold_group_haar_rightInvariant D
  exact fundamental_coset_probability_invariant D.Γ (nativeNilmanifoldGroupHaar D)
    (nativeNilmanifoldFundamentalDomain D) (native_nilmanifold_fundamental_domain_spec D).2.1

theorem native_nilmanifold_coset_borel {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    BorelSpace (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  exact CosetSpace.borelSpace

theorem native_nilmanifold_metric_coset_borel {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    BorelSpace (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @BorelSpace (D.G ⧸ D.Γ) t inferInstance) (nativeNilmanifold_metric_topology D))
      (native_nilmanifold_coset_borel D)

theorem native_nilmanifold_metric_quotient_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    CompactSpace (D.G ⧸ D.Γ) := by
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D)) D.quotientCompact

theorem native_nilmanifold_quotient_probability_translate {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (fun x : D.G ⧸ D.Γ => g • x) (nativeNilmanifoldQuotientProbability D) =
      nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI := native_nilmanifold_quotient_probability_invariant D
  exact (measurePreserving_smul g (nativeNilmanifoldQuotientProbability D)).map_eq

end Hindman168
