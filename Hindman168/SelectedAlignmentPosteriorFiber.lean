import Hindman168.SelectedAlignmentShortPosteriorTypical
import Hindman168.ConditionalProductFiberComparison

/-! Apply exact product Fubini to the ACTUAL short-exposure posterior.
The domination constant 3*2^|T| comes from the proved original master law,
before EVERY event/test/model. Conditional factors are not declared independent.
Native fiber bounds still require their actual source/geometry instantiation. -/
namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical

theorem selected_alignment_typical_short_posterior_fiber_union_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ (E : T → (T → ℕ) → Prop) (ε : ℝ),
      (∀ j : T, ∀ rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x k.val.val)))).support,
        event (uniformFinsetMass (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
          (fun value => E j (insertPivotCoordinate j rest value)) ≤ ε) →
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (fun y => ∃ j : T, E j (fun k : T => y k.val)) ≤
      (3*2^T.card)*(T.card : ℝ)*ε := by
  filter_upwards [selected_alignment_typicalShortPosterior_bound_eventually hF i gap hgap T hT] with w hw
  intro x hx htypical E ε hcap
  let μ : T → Mass ℕ := fun j => uniformFinsetMass
    (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val))
  have hμ (j : T) (value : ℕ) : 0 ≤ μ j value := uniformFinsetMass_nonneg _ _
  have ht (j : T) : total (μ j)=1 := by
    apply uniformFinsetMass_total
    apply Finset.card_pos.mpr
    exact ⟨x j.val,binaryDyadicResidueWindow_anchor (alignmentGlobalRawMass_support_positive hF w x hx j.val)⟩
  have hproduct := rough_pi_mass_coordinate_union_le μ E hμ ht (fun _ => ε) (by
    convert hcap using 1
    all_goals congr! 8)
  have hsum : (∑ _j : T, ε)=(T.card : ℝ)*ε := by simp
  rw [hsum] at hproduct
  have hposterior := hw x hx htypical (fun tail => ∃ j : T, E j tail)
  calc
    _ ≤ (3*2^T.card)*event (piMass μ) (fun tail => ∃ j : T, E j tail) := hposterior
    _ ≤ (3*2^T.card)*((T.card : ℝ)*ε) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by ring

end Hindman168
