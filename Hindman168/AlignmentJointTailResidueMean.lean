import Hindman168.AlignmentJointSourceRestriction
import Hindman168.AlignmentJointTailRemovalEvent
import Hindman168.AlignmentRetainedCubeNestedResidue
import Hindman168.NativeRealResidualGoodMean

/-! Literal normalized joint-source means on original retained CRT grids.
The source and endpoints are the SAME for every retained subset. Original
bad-event complements bound each exact one-factor mean difference. -/
namespace Hindman168
open Module FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

noncomputable def alignmentJointTailResidueMean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T U : Finset (Fin N)) (x : Fin N → ℕ)
    (d : ℕ) (Y rho : ℤ) (residueChoice : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (tail : T → ℕ) (lo hi : Option κ → ℤ)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi
    (alignmentRetainedCubeResidue (F.modulus w) d
      (alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U) Y rho residueChoice)
    (d*alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U : ℕ)))
    (fun y => obs (QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x
      shift weight g a tail (fun j => (y j : ℝ)))))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem alignment_tail_retained_insert_product (T U : Finset (Fin N)) (x : Fin N → ℕ)
    (tail : T → ℕ) (j : T) (hj : j.val ∉ U) :
    alignmentNaturalBlockProduct (alignmentTailTuple T x tail) (insert j.val U)=
      alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U*tail j := by
  rw [alignmentNaturalBlockProduct,Finset.prod_insert hj]
  rw [alignment_tail_tuple_inside]
  exact Nat.mul_comm _ _

theorem alignment_joint_tail_good_mean_difference
    (F : MasterParameterFamily) (q₀ w : ℕ) (T U : Finset (Fin N)) (x : Fin N → ℕ)
    (j : T) (hj : j.val ∉ U) (d : ℕ) (Y rho : ℤ) (residueChoice : Option κ → ℤ)
    (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (B : ι → ℝ) (L : ι → NNReal) (c C η : ℝ) (tail : T → ℕ)
    (hgood : ¬alignmentJointTailRemovalEvent D n v hv r b F q₀ w T U x j d Y rho residueChoice
      shift slots weight g a B L c C η tail)
    (hr : 0 < alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U)
    (hM : Nat.Coprime (F.modulus w : ℕ) (alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U))
    (hd : Nat.Coprime d (alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U))
    (hMf : Nat.Coprime (F.modulus w : ℕ) (alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U*tail j))
    (hdf : Nat.Coprime d (alignmentNaturalBlockProduct (alignmentTailTuple T x tail) U*tail j))
    (lo hi : Option κ → ℤ) :
    let y := alignmentTailTuple T x tail
    let retained := alignmentNaturalBlockProduct y U
    let q := d*retained
    let residue := alignmentRetainedCubeResidue (F.modulus w) d retained Y rho residueChoice
    let Z := alignmentCubeScale F w i T y/(q : ℝ)
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (∀ k, c*Z ≤ (hi k-(residue k : ℝ))/(q : ℝ)-(lo k-(residue k : ℝ))/(q : ℝ) ∧
      (hi k-(residue k : ℝ))/(q : ℝ)-(lo k-(residue k : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo k-(residue k : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi k-(residue k : ℝ))/(q : ℝ)| ≤ C*Z) →
    ∀ obs : C(J.G ⧸ J.Γ,ℂ), obs ∈ alignmentJointOriginalTestFamily D n v hv slots B L →
    ‖alignmentJointTailResidueMean D n v hv r b F q₀ w T (insert j.val U) x d Y rho residueChoice
      shift weight g a tail lo hi obs-
      alignmentJointTailResidueMean D n v hv r b F q₀ w T U x d Y rho residueChoice
      shift weight g a tail lo hi obs‖ < η := by
  dsimp only
  let y := alignmentTailTuple T x tail
  let retained := alignmentNaturalBlockProduct y U
  let q := d*retained
  let residue := alignmentRetainedCubeResidue (F.modulus w) d retained Y rho residueChoice
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro hgeom obs hobs
  have hg : ¬RoughNativeRealResidualTestFamilyLargeIndex J
      (alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j.val (fun k => (y k : ℝ)) shift weight g a)
      residue q (tail j) (tail j) (alignmentCubeScale F w i T y/(q : ℝ)) c C η
      (alignmentJointOriginalTestFamily D n v hv slots B L) := by
    simpa only [alignmentJointTailRemovalEvent,y,retained,q,residue,J,Nat.cast_mul] using hgood
  have hcompat := alignment_retained_cube_fine_coarse_compatible (F.modulus w) d retained (tail j)
    hr hM hd hMf hdf Y rho residueChoice
  have hh := native_real_residual_good_integer_mean J _ residue q (tail j) (tail j)
    (alignmentCubeScale F w i T y/(q : ℝ)) c C η _ obs hobs hg lo hi
    (alignmentRetainedCubeResidue (F.modulus w) d (retained*tail j) Y rho residueChoice) hgeom hcompat
  dsimp only [y] at hh
  simp_rw [alignment_joint_removed_native_actual_tail_spatial_source] at hh
  simpa only [alignmentJointTailResidueMean,y,retained,q,residue,alignment_tail_retained_insert_product T U x tail j hj,Nat.mul_assoc] using hh

end Hindman168
