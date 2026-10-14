import Hindman168.AlignmentOriginalJointLinearOrbit
import Hindman168.AlignmentLocalLength

/-! The real source is the genuine logarithmic extension of the SAME original
joint integer orbit. The local-length growth is inherited from the actual
master microcell lengths, along any cofinal width sequence. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentOriginalJointRealSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (t : ℝ) : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeLieExponential (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E) (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I) (G := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (roughVectorMvEval (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E) (nativeOriginalLeftLinearLog (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)))
      (alignmentOriginalJointPointStep D n v hv T y g)
      (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)) (fun _ => t))

theorem alignment_original_joint_real_source_integer
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (z : ℤ) :
    alignmentOriginalJointRealSource D n v hv F q₀ w T y p shift g a (z : ℝ) =
      alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a z :=
  alignment_original_joint_point_orbit_log_source D n v hv F q₀ w T y p shift g a z

theorem alignment_local_length_cofinal {k : ℕ} {A : Finset ℚ}
    {P : Finset (MvPolynomial (Fin k) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (i : Fin N)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop) :
    Tendsto (fun m => (alignmentLocalLength F (w m) i : ℝ)) atTop atTop :=
  tendsto_atTop.2 (fun C => hw.eventually (alignmentLocalLength_eventually_large hF i C))

end Hindman168
