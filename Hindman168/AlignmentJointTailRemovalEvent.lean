import Hindman168.AlignmentJointOriginalTestWindow
import Hindman168.AlignmentJointSourceTailDependence
import Hindman168.AlignmentTailRestRetainedArithmetic

/-! The actual one-factor original-test event, with literal retained q and
CRT residue vector and actual normalized cube scale. Every tail sample is
kept; its other factors determine the source and coarse class before t varies. -/
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

noncomputable def alignmentJointTailRemovalEvent
    (F : MasterParameterFamily) (q₀ w : ℕ) (T U : Finset (Fin N)) (x : Fin N → ℕ)
    (j : T) (d : ℕ) (Y rho : ℤ) (residueChoice : Option κ → ℤ)
    (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (B : ι → ℝ) (L : ι → NNReal) (c C η : ℝ)
    (tail : T → ℕ) : Prop := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let y := alignmentTailTuple T x tail
  let retained := alignmentNaturalBlockProduct y U
  let Q := alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j.val (fun k => (y k : ℝ)) shift weight g a
  exact RoughNativeRealResidualTestFamilyLargeIndex J Q
    (alignmentRetainedCubeResidue (F.modulus w) d retained Y rho residueChoice) (d*retained)
    (tail j) (tail j) (alignmentCubeScale F w i T y/((d : ℝ)*retained)) c C η
    (alignmentJointOriginalTestFamily D n v hv slots B L)

theorem alignment_joint_tail_removal_fiber_event_bound
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C η : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η)
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ U : Finset (Fin N), U ⊆ T → ∀ j : T, j.val ∉ U →
      ∀ rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x k.val.val)))).support,
      ∀ (q₀ : ℕ) (Y rho : ℤ) (residueChoice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      event (uniformFinsetMass (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
        (fun t => alignmentJointTailRemovalEvent D n v hv r b F q₀ w T U x j d Y rho residueChoice
          shift slots weight g a B L c C η (insertPivotCoordinate j rest t)) ≤ δ := by
  obtain ⟨B',L',hB',hL',hh⟩ := alignment_joint_removed_original_test_window_all_anchors (κ := κ) D n v hv r b
    hF T hT d hd ((2 : ℝ)^T.card) (((2 : ℝ)^T.card)^2) c C η
    (by positivity) (by have hpow : (1 : ℝ) ≤ 2^T.card := one_le_pow₀ (by norm_num); nlinarith)
    hc hC hη hδ slots B L
  filter_upwards [hh,eventually_ge_atTop (max d 1)] with w hw hwlarge
  intro x hx htyp U hU j hj rest hrest q₀ Y rho residueChoice shift weight g a
  let modulus : ℕ := (F.modulus w : ℕ)*(primorial w)^w
  let y := alignmentTailTuple T x (insertPivotCoordinate j rest (x j.val))
  let retained := alignmentNaturalBlockProduct y U
  let q := d*retained
  let residue := alignmentRetainedCubeResidue (F.modulus w) d retained Y rho residueChoice
  let Zactual := fun t => alignmentCubeScale F w i T
    (alignmentTailTuple T x (insertPivotCoordinate j rest t))/((d : ℝ)*retained)
  have har := alignment_tail_rest_retained_arithmetic hF w d hd
    ((le_max_left d 1).trans hwlarge) ((le_max_right d 1).trans hwlarge) T U hU x hx j rest hrest
  have hq : 0 < q := Nat.mul_pos hd har.1
  have hZ : ∀ t ∈ binaryDyadicResidueWindow modulus (x j.val),
      alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*2^T.card) ≤ Zactual t ∧
      Zactual t ≤ ((2 : ℝ)^T.card)^2*
        (alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*2^T.card)) := by
    intro t ht
    have hs := alignment_tail_rest_retained_scale_range F w i T U hU x modulus d hd
      (fun k _ => alignmentGlobalRawMass_support_positive hF w x hx k) j rest hrest t ht
    dsimp only at hs ⊢
    rw [alignment_tail_rest_retained_product T U x j hj rest (x j.val) t] at hs
    exact hs
  have hcap := hw x hx htyp U hU j q residue hq q₀ (fun k => (y k : ℝ))
    shift weight g a Zactual hZ
  apply le_trans _ hcap.le
  apply event_mono _ (uniformFinsetMass_nonneg _)
  intro t ht
  change RoughNativeRealResidualTestFamilyLargeIndex _ _ _ _ _ _ _ _ _ _ _ at ht
  have hretained := alignment_tail_rest_retained_product T U x j hj rest (x j.val) t
  have hsource := alignment_joint_removed_native_source_tail_congr D n v hv r b
    F q₀ w T x j.val
    (fun k => (alignmentTailTuple T x (insertPivotCoordinate j rest t) k : ℝ))
    (fun k => (y k : ℝ)) (by
      intro k hk hkj
      rw [alignment_tail_rest_tuple_update T x j rest (x j.val) t,Function.update_of_ne hkj])
    shift weight g a
  simpa only [alignmentJointTailRemovalEvent,hretained,hsource,insertPivotCoordinate_self] using ht

end Hindman168
