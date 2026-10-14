import Hindman168.AlignmentJointTailResidueMean
import Hindman168.AlignmentOriginalDenominatorChoices
import Hindman168.AlignmentSingleCoordinateTranslation

/-! Terminal retained-empty mean is EXACTLY the original denominator d grid.
Its genuine spatial translation has the original normalized boundary-count
bound, without an assumed Lipschitz property of the actual source or reading. -/
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

noncomputable def alignmentJointDenominatorSpatialMean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ) (d : ℕ)
    (choice : Option κ → ℤ) (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (tail : T → ℕ) (lo hi : Option κ → ℤ)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi choice d))
    (fun z => obs (QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x
      shift weight g a tail (fun j => (z j : ℝ)))))

noncomputable def alignmentJointTranslatedDenominatorMean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ) (d : ℕ)
    (choice : Option κ → ℤ) (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (tail : T → ℕ) (lo hi displacement : Option κ → ℤ)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi choice d))
    (fun z => obs (QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x
      shift weight g a tail (fun j => (z j+displacement j : ℤ)))))

theorem alignment_joint_terminal_grid_mean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (d : ℕ) (Y rho : ℤ) (choice : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (tail : T → ℕ) (lo hi : Option κ → ℤ)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ) :
    alignmentJointTailResidueMean D n v hv r b F q₀ w T ∅ x d Y rho choice shift weight g a tail lo hi obs=
      alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a tail lo hi obs := by
  simp only [alignmentJointTailResidueMean,alignmentJointDenominatorSpatialMean,
    alignmentNaturalBlockProduct,Finset.prod_empty,Nat.mul_one,alignment_terminal_cube_residue_box]

theorem alignment_joint_terminal_single_translation_bound
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (d : ℕ) (hd : 0 < d) (choice : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (tail : T → ℕ) (lo hi : Option κ → ℤ) (coordinate : Option κ) (delta : ℤ)
    (hdelta : (d : ℤ) ∣ delta) (Z c K : ℝ) (hcZ : 0 < c*Z) (hdZ : 2*(d : ℝ) ≤ c*Z)
    (hlen : ∀ j, c*Z ≤ (hi j : ℝ)-(lo j : ℝ)) (hK : 0 ≤ K)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ)
    (hobs : ∀ z, ‖obs z‖ ≤ K) :
    ‖alignmentJointTranslatedDenominatorMean D n v hv r b F q₀ w T x d choice shift weight g a tail lo hi
        (fun j => if j=coordinate then delta else 0) obs-
      alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a tail lo hi obs‖ ≤
      4*K*|(delta : ℝ)|/(c*Z) := by
  let f : (Option κ → ℤ) → ℂ := fun z => obs (QuotientGroup.mk
    (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x shift weight g a tail (fun j => (z j : ℝ))))
  have hf : ∀ z, ‖f z‖ ≤ K := fun z => hobs _
  let u : Option κ → ℤ := fun j => if j=coordinate then delta else 0
  have hu : ∀ j, (d : ℤ) ∣ u j := by
    intro j
    dsimp only [u]
    split_ifs
    · exact hdelta
    · exact dvd_zero (d : ℤ)
  have hh := alignment_residue_box_translation_scale_bound (ι := Option κ) lo hi choice u d
    (by exact_mod_cast hd) hu Z c hcZ hdZ hlen f K hK hf
  have hsum : (∑ j, |(u j : ℝ)|)=|(delta : ℝ)| := by
    simp only [u,Int.cast_ite,Int.cast_zero,apply_ite abs,abs_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hsum] at hh
  unfold alignmentJointTranslatedDenominatorMean alignmentJointDenominatorSpatialMean
  rw [complexExpectation_uniformFinset,complexExpectation_uniformFinset]
  exact hh

end Hindman168
