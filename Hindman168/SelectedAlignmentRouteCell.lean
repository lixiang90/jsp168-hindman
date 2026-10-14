import Hindman168.SelectedAlignmentRouteNumerical
import Hindman168.PositivePrincipalSumHarmonicCellEmpirical
import Hindman168.SelectedPrincipalMicrocellGrowth

namespace Hindman168
open Filter MeasureTheory FiniteMass
open scoped Topology ENNReal Classical

/-- The original conditional uniform pivot law on the selected padding
microcell. Its fallback matters only when the window is empty, which is
excluded eventually by the actual master growth theorem. -/
noncomputable def selectedAlignmentRawCellProbability {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (w : ℕ) (x : Fin M → ℕ) : ProbabilityMeasure ℤ :=
  finiteEmpiricalProbability (Finset.Ico 0 (selectedPrincipalMicrocellLength F e w i : ℤ))
    (fun ell => alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i)
      (F.modulus w) (x (principalAlignmentEmbedding e heM i)) + (F.modulus w : ℤ)*ell) 0

noncomputable def selectedAlignmentRawRouteCellMass {n M : ℕ} {κ : Type*}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w : ℕ) (x : Fin M → ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) : ℝ≥0∞ :=
  (selectedAlignmentRawCellProbability F e heM i w x : Measure ℤ)
    (selectedAlignmentRouteActualSet
      (selectedAlignmentRouteRawReading (principalAlignmentEmbedding e heM) i F q₀ w x S)
      θ q₀ plan b requests (principalPivotRoutes plan))

theorem selected_alignment_raw_cell_event_toReal {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (w : ℕ) (x : Fin M → ℕ)
    (hlen : 0 < selectedPrincipalMicrocellLength F e w i) (E : Set ℤ) :
    ((selectedAlignmentRawCellProbability F e heM i w x : Measure ℤ) E).toReal =
      event (uniformIntervalMass 0 (selectedPrincipalMicrocellLength F e w i))
        (fun ell => alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i)
          (F.modulus w) (x (principalAlignmentEmbedding e heM i)) +
          (F.modulus w : ℤ)*ell ∈ E) := by
  simp only [selectedAlignmentRawCellProbability, uniformIntervalMass, integerWindow, zero_add]
  apply principal_empirical_event_toReal
  · exact Finset.nonempty_Ico.mpr (by exact_mod_cast hlen)
  · exact Set.to_countable E |>.measurableSet

/-- Equality of literal prelimit events at every sampled integer gives
exact equality of the two empirical probabilities. -/
theorem selected_alignment_empirical_event_congr {Z X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : Finset Z) (hS : S.Nonempty) (f : Z → X) (g : Z → Y)
    (x₀ : X) (y₀ : Y) (E : Set X) (F : Set Y)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (heq : ∀ z ∈ S, f z ∈ E ↔ g z ∈ F) :
    (finiteEmpiricalProbability S f x₀ : Measure X) E =
      (finiteEmpiricalProbability S g y₀ : Measure Y) F := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [principal_empirical_event_toReal S hS f x₀ E hE,
    principal_empirical_event_toReal S hS g y₀ F hF]
  unfold uniformFinsetMass
  rw [event_eq_sum _ _ (flatMass_support S _), event_eq_sum _ _ (flatMass_support S _)]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [heq z hz]

theorem selected_alignment_route_actual_measurable {n : ℕ} {i : Fin n} {X κ : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [Finite κ]
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (hc : ∀ B a c stored query, Continuous (read B a c stored query))
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) :
    MeasurableSet (selectedAlignmentRouteActualSet read θ q₀ plan b requests routes) := by
  rw [← selected_alignment_route_actual_comparisons]
  unfold principalActualComparisons
  simp only [Set.setOf_exists, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro route
  apply MeasurableSet.iInter
  intro j
  have he : {x | 2*θ < selectedAlignmentRouteCenter read q₀ plan b requests route.val j x →
        θ < selectedAlignmentRouteTerminal read q₀ plan b requests route.val j x} =
      {x | selectedAlignmentRouteCenter read q₀ plan b requests route.val j x ≤ 2*θ} ∪
      {x | θ < selectedAlignmentRouteTerminal read q₀ plan b requests route.val j x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, imp_iff_not_or, not_lt]
  rw [he]
  exact (isClosed_le (hc _ _ _ _ _) continuous_const).measurableSet.union
    (isOpen_lt continuous_const (hc _ _ _ _ _)).measurableSet

end Hindman168
