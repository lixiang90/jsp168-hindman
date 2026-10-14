import Hindman168.AlignmentJointTailResidueMean
import Hindman168.AlignmentActualOriginalResidualGeometry
import Hindman168.AlignmentTailTupleOriginalData

/-! Exact one-factor mean comparison on the ORIGINAL permitted cube boxes.
Actual raw supports derive normalization geometry and all fine/coarse CRT
arithmetic. The only probabilistic input is the genuine bad-event complement. -/
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

theorem alignment_joint_actual_removal_step_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (η : ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      ∀ y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y →
      ∀ lower upper : Option κ → ℝ,
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) →
      ∀ U : Finset (Fin N), U ⊆ T → ∀ j : T, j.val ∉ U →
      ∀ (q₀ : ℕ) (rho : ℤ) (residueChoice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
      let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
      let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
      ¬alignmentJointTailRemovalEvent D n v hv r b F q₀ w T U x j d Y rho residueChoice
        shift slots weight g a B L (c/2) (alignmentOriginalResidualUpper T.card K C) η (fun k : T => y k.val) →
      ∀ obs : C(J.G ⧸ J.Γ,ℂ), obs ∈ alignmentJointOriginalTestFamily D n v hv slots B L →
      ‖alignmentJointTailResidueMean D n v hv r b F q₀ w T (insert j.val U) x d Y rho residueChoice
        shift weight g a (fun k : T => y k.val) lo hi obs-
        alignmentJointTailResidueMean D n v hv r b F q₀ w T U x d Y rho residueChoice
        shift weight g a (fun k : T => y k.val) lo hi obs‖ < η := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  filter_upwards [alignment_actual_original_residual_geometry_eventually (κ := κ) hF i T hT d hd c C K hc hC hK,
    eventually_ge_atTop d] with w hw hwd
  intro x hx y hy hkey lower upper hbox U hU j hj q₀ rho residueChoice shift weight g a hgood obs hobs
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let retained := alignmentNaturalBlockProduct y U
  have hret : 0 < retained := Finset.prod_pos (fun z _ => alignmentGlobalRawMass_support_positive hF w y hy z)
  have hcoarse := alignmentMaster_retained_coprime hF w d hd hwd y U
    (fun z _ => alignmentGlobalRawMass_support_coprime F w y hy z)
  have hfin := alignmentMaster_retained_coprime hF w d hd hwd y (insert j.val U)
    (fun z _ => alignmentGlobalRawMass_support_coprime F w y hy z)
  have hprod : alignmentNaturalBlockProduct y (insert j.val U)=retained*y j.val := by
    rw [alignmentNaturalBlockProduct,Finset.prod_insert hj]
    exact Nat.mul_comm _ _
  rw [hprod] at hfin
  have hstart := alignmentShortExposureKey_start_eq F w i T hkey
  have hbounds := alignment_retained_cube_residue_bounds (F.modulus w) d retained hd hret Y rho residueChoice
  have hgeometry := hw y hy lower upper hbox U hU
    (alignmentRetainedCubeResidue (F.modulus w) d retained Y rho residueChoice) hbounds
  dsimp only at hgeometry
  rw [←hstart] at hgeometry
  apply alignment_joint_tail_good_mean_difference D n v hv r b F q₀ w T U x j hj d Y rho residueChoice
    shift slots weight g a B L (c/2) (alignmentOriginalResidualUpper T.card K C) η (fun k : T => y k.val) hgood
  · simpa only [alignment_tail_tuple_original_product T U hU] using hret
  · simpa only [alignment_tail_tuple_original_product T U hU] using hcoarse.1
  · simpa only [alignment_tail_tuple_original_product T U hU] using hcoarse.2
  · simpa only [alignment_tail_tuple_original_product T U hU] using hfin.1
  · simpa only [alignment_tail_tuple_original_product T U hU] using hfin.2
  · simpa only [alignment_tail_tuple_original_product T U hU,alignment_tail_tuple_original_cube_scale] using hgeometry
  · exact hobs

end Hindman168
