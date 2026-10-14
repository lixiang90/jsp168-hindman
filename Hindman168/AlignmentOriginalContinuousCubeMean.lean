import Hindman168.AlignmentJointOriginalProductCubeMean
import Hindman168.FinitePiProductLinearApproximation
import Hindman168.ComplexMeanObservableApproximation

/-! EVERY original continuous cube test has a literal mean on the complete
finite tuple of original nilsequence slot readings. Product tests recover
exactly the registered original product law; uniform approximations control
both own-face means with unchanged boxes and zero means on empty grids. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical
universe u
variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (q₀ w : ℕ)
  (T : Finset (Fin N)) (y : Fin N → ℕ) (p : ℤ) (d : ℕ)
  (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
  (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
  (g a : ∀ ν, (D ν).G)

noncomputable def alignmentOriginalCubeReading (ell : Option κ → ℤ) : ∀ ν, (D ν).G ⧸ (D ν).Γ :=
  fun ν => (g ν ^ (alignmentIntegerArrayArgument y (F.modulus w)
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
    (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
    (p+(F.modulus w : ℤ)*(ell none+∑ j, weight ν j*ell (some j)))
    (shift ν) (slots ν)/(F.modulus w : ℤ)) * a ν : (D ν).G ⧸ (D ν).Γ)

noncomputable def alignmentOriginalContinuousCubeMean
    (obs : (∀ ν, (D ν).G ⧸ (D ν).Γ) → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass
    (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d))
    (fun ell => obs (alignmentOriginalCubeReading D F q₀ w T y p shift slots weight g a ell))

theorem alignment_original_continuous_cube_product_mean :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a
        (finitePiComplexProduct (fun ν => (D ν).G ⧸ (D ν).Γ) obs)=
      alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a
        (fun ν => obs ν) := by
  intro obs
  unfold alignmentOriginalContinuousCubeMean alignmentOriginalProductCubeMean
  congr 1
  funext ell
  rw [finite_pi_complex_product_apply]
  rfl

omit [Fintype ι] in
theorem alignment_original_continuous_cube_mean_approximation :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ (obs approx : C((∀ ν, (D ν).G ⧸ (D ν).Γ),ℂ)) (ε : ℝ), 0 ≤ ε → ‖obs-approx‖ ≤ ε →
      ‖alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a obs-
        alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a approx‖ ≤ ε := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro obs approx ε hε hclose
  unfold alignmentOriginalContinuousCubeMean
  apply complex_uniform_mean_observable_difference _ _ _ ε hε
  intro ell _hell
  exact (ContinuousMap.norm_coe_le_norm (obs-approx) _).trans hclose

omit [Fintype ι] in
theorem alignment_original_continuous_cube_face_approximation
    (faceSlots : ι → AlignmentAddingPair N i → ℤ) :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ (obs approx : C((∀ ν, (D ν).G ⧸ (D ν).Γ),ℂ)) (η : ℝ), 0 < η → ‖obs-approx‖ < η/4 →
      η ≤ ‖alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a obs-
        alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a obs‖ →
      η/2 ≤ ‖alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a approx-
        alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a approx‖ := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro obs approx η hη hclose hbad
  have h0 := alignment_original_continuous_cube_mean_approximation D F q₀ w T y p d ellResidue lower upper
    shift slots weight g a obs approx (η/4) (by positivity) hclose.le
  have h1 := alignment_original_continuous_cube_mean_approximation D F q₀ w T y p d ellResidue lower upper
    shift faceSlots weight g a obs approx (η/4) (by positivity) hclose.le
  let O0 := alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a obs
  let O1 := alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a obs
  let A0 := alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a approx
  let A1 := alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a approx
  have htri : ‖O1-O0‖ ≤ ‖O1-A1‖+‖A1-A0‖+‖A0-O0‖ :=
    (norm_sub_le_norm_sub_add_norm_sub O1 A1 O0).trans
      (by linarith [norm_sub_le_norm_sub_add_norm_sub A1 A0 O0])
  rw [norm_sub_rev A0 O0] at htri
  change ‖O0-A0‖ ≤ η/4 at h0
  change ‖O1-A1‖ ≤ η/4 at h1
  change η ≤ ‖O1-O0‖ at hbad
  change η/2 ≤ ‖A1-A0‖
  linarith

end Hindman168
