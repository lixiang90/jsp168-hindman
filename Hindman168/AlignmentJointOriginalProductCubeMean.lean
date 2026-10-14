import Hindman168.AlignmentJointFullSpatialReadings
import Hindman168.AlignmentJointTailResidueMean
import Hindman168.AlignmentTailTupleOriginalData
import Hindman168.AlignmentOriginalCubeCRTMean

/-! Literal ORIGINAL nilsequence product cube average equals its COMPLETE
joint full-tail CRT mean. Actual raw supports and exposed residue identities
discharge all sampling conditions; no original observation is replaced. -/
namespace Hindman168
open Module FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

noncomputable def alignmentOriginalProductCubeMean {ι : Type} [Fintype ι]
    {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (q₀ w : ℕ)
    (T : Finset (Fin N)) (y : Fin N → ℕ) (p : ℤ) (d : ℕ)
    (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (obs : ∀ ν, ((D ν).G ⧸ (D ν).Γ) → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass
    (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d))
    (fun ell => ∏ ν, obs ν ((g ν ^ (alignmentIntegerArrayArgument y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
      (p+(F.modulus w : ℤ)*(ell none+∑ j, weight ν j*ell (some j)))
      (shift ν) (slots ν)/(F.modulus w : ℤ)) * a ν : (D ν).G ⧸ (D ν).Γ)))


variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_original_product_cube_mean_full_crt
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w) (d : ℕ) (hd : 0 < d) (hwd : d ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) (x y : Fin N → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support)
    (hy : y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support)
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (ellResidue choice : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let rho := alignmentPivotArrayResidue x T (F.modulus w) (x i) 0
    let lo := fun j => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y j ⌈lower j⌉
    let hi := fun j => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y j ⌈upper j⌉
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (∀ j, Int.ModEq d (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y j (ellResidue j)) (choice j)) →
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a (fun ν => obs ν)=
      alignmentJointTailResidueMean D n v hv r b F q₀ w T T x d Y rho choice shift weight g a
        (fun k : T => y k.val) lo hi (alignmentJointNativeMetricProduct D n v hv slots obs) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro hchoice obs
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let rho := alignmentPivotArrayResidue x T (F.modulus w) (x i) 0
  let f : (Option κ → ℤ) → ℂ := fun z => alignmentJointNativeMetricProduct D n v hv slots obs
    (QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x shift weight g a
      (fun k : T => y k.val) (fun j => (z j : ℝ))))
  have hpos : 0 < alignmentNaturalBlockProduct y T :=
    Finset.prod_pos (fun j _ => alignmentGlobalRawMass_support_positive hF w y hy j)
  have hcop := alignmentMaster_retained_coprime hF w d hd hwd y T
    (fun j _ => alignmentGlobalRawMass_support_coprime F w y hy j)
  have hrho : ((alignmentNaturalBlockProduct y T : ℤ)*p) % (F.modulus w : ℤ)=rho := by
    simpa only [rho,alignmentPivotArrayResidue,add_zero] using
      alignmentShortExposureKey_arrayResidue_eq F w i T hT hkey p 0 hp
  have hmean := alignment_original_cube_crt_complex_mean (F.modulus w) d (alignmentNaturalBlockProduct y T)
    hpos hcop.1 hcop.2 p Y rho hrho lower upper ellResidue choice hchoice f
  have he : alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a (fun ν => obs ν)=
      complexExpectation (uniformFinsetMass (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d))
        (fun ell => f (fun j => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y j (ell j))) := by
    unfold alignmentOriginalProductCubeMean
    congr 1
    funext ell
    have hcoord : (fun j : Option κ => (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y j (ell j) : ℝ)) =
        (fun j : Option κ => match j with
          | none => (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct y T) p Y (ell none) : ℝ)
          | some j => (((alignmentNaturalBlockProduct y T : ℤ)*ell (some j) : ℤ) : ℝ)) := by
      funext j; cases j <;> rfl
    dsimp only [f]
    rw [hcoord]
    exact (alignment_joint_full_spatial_original_product_sample D n v hv r b hF hq hw T hT
      (alignmentGlobalRawMass_support_coprime F w x hx) (alignmentGlobalRawMass_support_coprime F w y hy)
      hkey p (ell none) hp (fun j => ell (some j)) weight shift slots g a obs).symm
  rw [he,hmean]
  simp only [alignmentJointTailResidueMean,alignment_tail_tuple_original_product T T (Finset.Subset.refl T)]
  rfl

end Hindman168
