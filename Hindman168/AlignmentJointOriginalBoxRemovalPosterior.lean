import Hindman168.AlignmentJointOriginalBoxRemovalFailure
import Hindman168.AlignmentJointTailRemovalPosterior
import Hindman168.FiniteSupportedEventComparison

/-! COMPLETE original permitted-box joint mean removal has vanishing failure
under the ACTUAL short-exposure posterior. Geometry, every source/grid
comparison and the literal telescope are proved dependencies, not input caps. -/
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

theorem alignment_joint_original_box_removal_posterior_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ (q₀ : ℕ) (rho : ℤ) (residueChoice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x))
        (alignmentJointOriginalBoxRemovalFailure D n v hv r b F q₀ w T x d Y rho residueChoice
          shift slots weight g a B L c C ε) < δ := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let η := ε/((T.card : ℝ)+1)
  have hη : 0 < η := div_pos hε (by positivity)
  have he : ((T.card : ℝ)+1)*η=ε := by dsimp only [η]; field_simp
  have hmargin : (T.card : ℝ)*η < ε := by nlinarith
  have hC' : 0 ≤ alignmentOriginalResidualUpper T.card K C := by
    unfold alignmentOriginalResidualUpper
    exact le_trans (by positivity) (le_max_right _ _)
  have hp := alignment_joint_tail_removal_posterior_uniform_vanishing (κ := κ) D n v hv r b
    hF T hT d hd (c/2) (alignmentOriginalResidualUpper T.card K C) η (by positivity) hC' hη slots B L hδ
  have hchain := alignment_joint_actual_removal_chain_eventually (κ := κ) D n v hv r b
    hF T hT d hd c C K hc hC hK slots B L η
  filter_upwards [hp,hchain,alignmentGlobalRawMass_geometry hF] with w hw hcstep hraw
  intro x hx htyp q₀ rho residueChoice shift weight g a
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x)
  let E : (Fin N → ℕ) → Prop := fun y => ∃ j : T,
    alignmentJointTailRemovalEvent D n v hv r b F q₀ w T (orderedRetainedTail T j.val) x j d Y rho residueChoice
      shift slots weight g a B L (c/2) (alignmentOriginalResidualUpper T.card K C) η (fun k : T => y k.val)
  have hcap : event μ E < δ := hw x hx htyp (fun j : T => orderedRetainedTail T j.val)
    (fun j => ⟨ordered_retained_tail_subset T j.val,ordered_retained_tail_excludes T j.val⟩)
    q₀ Y rho (fun _ => residueChoice) shift weight g a
  apply lt_of_le_of_lt _ hcap
  apply event_mono_on_support μ _ E (conditionMass_nonneg _ _ hraw.1)
  intro y hy hbad
  have hyr := conditionMass_support _ _ hy
  have hykey : alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x := by
    by_contra hn
    have hh := Finsupp.mem_support_iff.mp hy
    rw [conditionMass_apply,if_neg hn] at hh
    exact hh rfl
  obtain ⟨lower,upper,obs,hbox,hobs,hlarge⟩ := hbad
  by_contra hno
  have hgood : ∀ j : T, ¬alignmentJointTailRemovalEvent D n v hv r b F q₀ w T
      (orderedRetainedTail T j.val) x j d Y rho residueChoice shift slots weight g a B L
      (c/2) (alignmentOriginalResidualUpper T.card K C) η (fun k : T => y k.val) :=
    fun j hj => hno ⟨j,hj⟩
  have hsmall := hcstep x hx y hyr hykey.symm lower upper hbox q₀ rho residueChoice shift weight g a hgood obs hobs
  exact (not_le_of_gt (hsmall.trans_lt hmargin)) hlarge

end Hindman168
