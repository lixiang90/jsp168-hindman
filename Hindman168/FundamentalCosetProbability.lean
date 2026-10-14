import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic

namespace Hindman168
open Set MeasureTheory Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

noncomputable def fundamentalCosetMeasure (Γ : Subgroup G) (ν : Measure G) (F : Set G) :
    Measure (G ⧸ Γ) := Measure.map ((↑) : G → G ⧸ Γ) (ν.restrict F)

noncomputable def fundamentalCosetProbability (Γ : Subgroup G) (ν : Measure G) (F : Set G) :
    Measure (G ⧸ Γ) := (ν F)⁻¹ • fundamentalCosetMeasure Γ ν F

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem fundamental_coset_measure_univ (Γ : Subgroup G) (ν : Measure G) (F : Set G) :
    fundamentalCosetMeasure Γ ν F Set.univ = ν F := by
  have hπ : Measurable ((↑) : G → G ⧸ Γ) := QuotientGroup.measurable_coe
  rw [fundamentalCosetMeasure, Measure.map_apply hπ MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem fundamental_coset_probability_isProbability (Γ : Subgroup G) (ν : Measure G) (F : Set G)
    (hpos : 0 < ν F) (hfin : ν F < ⊤) : IsProbabilityMeasure (fundamentalCosetProbability Γ ν F) := by
  refine ⟨?_⟩
  rw [fundamentalCosetProbability, Measure.smul_apply, fundamental_coset_measure_univ]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

theorem fundamental_coset_measure_invariant [PolishSpace G] (Γ : Subgroup G)
    [IsClosed (Γ : Set G)] [Countable Γ] (ν : Measure G)
    [IsMulLeftInvariant ν] [IsMulRightInvariant ν] (F : Set G)
    (hF : IsFundamentalDomain Γ.op F ν) : SMulInvariantMeasure G (G ⧸ Γ) (fundamentalCosetMeasure Γ ν F) := by
  letI : BorelSpace (G ⧸ Γ) := CosetSpace.borelSpace
  letI : HasFundamentalDomain Γ.op G ν := ⟨F, hF⟩
  letI : QuotientMeasureEqMeasurePreimage ν (fundamentalCosetMeasure Γ ν F) :=
    hF.quotientMeasureEqMeasurePreimage_quotientMeasure
  exact QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient ν

theorem fundamental_coset_probability_invariant [PolishSpace G] (Γ : Subgroup G)
    [IsClosed (Γ : Set G)] [Countable Γ] (ν : Measure G)
    [IsMulLeftInvariant ν] [IsMulRightInvariant ν] (F : Set G)
    (hF : IsFundamentalDomain Γ.op F ν) :
    SMulInvariantMeasure G (G ⧸ Γ) (fundamentalCosetProbability Γ ν F) := by
  letI := fundamental_coset_measure_invariant Γ ν F hF
  exact SMulInvariantMeasure.smul (ν F)⁻¹

theorem fundamental_coset_probability_domain_independent (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [IsMulRightInvariant ν] (F F' : Set G)
    (hF : IsFundamentalDomain Γ.op F ν) (hF' : IsFundamentalDomain Γ.op F' ν) :
    fundamentalCosetProbability Γ ν F = fundamentalCosetProbability Γ ν F' := by
  have hraw : fundamentalCosetMeasure Γ ν F = fundamentalCosetMeasure Γ ν F' :=
    hF.quotientMeasure_eq ν hF'
  have hmass := congrArg (fun μ : Measure (G ⧸ Γ) => μ Set.univ) hraw
  rw [fundamental_coset_measure_univ, fundamental_coset_measure_univ] at hmass
  simp only [fundamentalCosetProbability, hmass, hraw]

end Hindman168
