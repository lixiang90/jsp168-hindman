import Hindman168.AlignmentOriginalProductRemovalFailure
import Hindman168.AlignmentJointOriginalBoxRemovalFiniteChoices

/-! Original product-observation cube law and its genuine denominator-only
law agree in probability under the ACTUAL posterior, uniformly in original
boxes, residues and bounded tests. Sample-selected denominator choices are
covered by a fixed finite list; the origin stays genuinely exposed. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_original_product_removal_posterior_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x))
        (alignmentOriginalProductRemovalFailure D n v hv r b F q₀ w T x d hd shift slots weight g a B L c C ε) < δ := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have hh := alignment_joint_original_box_removal_finite_choices (κ := κ) (χ := Option κ → Fin d) D n v hv r b
    hF T hT d hd c C K hc hC hK slots B L hε hδ
  filter_upwards [hh,eventually_ge_atTop (q₀+1),eventually_ge_atTop d,alignmentGlobalRawMass_geometry hF]
    with w hw hwq hwd hraw
  intro x hx htyp shift weight g a
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let rho := alignmentPivotArrayResidue x T (F.modulus w) (x i) 0
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x)
  let E : (Fin N → ℕ) → Prop := fun y => ∃ choice : Option κ → Fin d,
    alignmentJointOriginalBoxRemovalFailure D n v hv r b F q₀ w T x d Y rho
      (alignmentDenominatorChoice choice) shift slots weight g a B L c C ε y
  have hcap : event μ E < δ := hw x hx htyp q₀ rho alignmentDenominatorChoice shift weight g a
  apply lt_of_le_of_lt _ hcap
  apply event_mono_on_support μ _ E (conditionMass_nonneg _ _ hraw.1)
  intro y hy hbad
  have hyr := conditionMass_support _ _ hy
  have hykey : alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x := by
    by_contra hn
    have hnz := Finsupp.mem_support_iff.mp hy
    rw [conditionMass_apply,if_neg hn] at hnz
    exact hnz rfl
  obtain ⟨lower,upper,ellResidue,obs,hbox,hobs,hlarge⟩ := hbad
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let choice := alignmentDenominatorRemainder d hd
    (fun z : Option κ => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z (ellResidue z))
  have hp : Int.ModEq (F.modulus w : ℕ) p (y i) := alignmentMicrocellFirst_modEq _ _ _
  have hmean := alignment_original_product_cube_mean_full_crt D n v hv r b hF hq hwq d hd hwd T hT x y hx hyr
    hykey.symm p hp ellResidue (alignmentDenominatorChoice choice) lower upper shift slots weight g a
    (alignment_denominator_remainder_class d hd _) obs
  refine ⟨choice,lower,upper,alignmentJointNativeMetricProduct D n v hv slots obs,hbox,?_,?_⟩
  · exact ⟨obs,(fun ν _ => hobs ν),rfl⟩
  · rw [hmean] at hlarge
    rw [←alignment_joint_terminal_grid_mean D n v hv r b F q₀ w T x d Y rho (alignmentDenominatorChoice choice)
      shift weight g a (fun k : T => y k.val)] at hlarge
    exact hlarge

end Hindman168
