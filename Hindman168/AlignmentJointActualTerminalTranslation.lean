import Hindman168.AlignmentJointTerminalGridMeans
import Hindman168.AlignmentJointMetricProductBounds
import Hindman168.AlignmentCanonicalShiftScale

/-! ACTUAL master Delta shifts preserve the terminal d grid and have uniformly
vanishing boundary-count error on every original permitted box and original
joint test. Divisibility, growth, source reading bound and nonempty geometry
are derived, not supplied as desired analytic hypotheses. -/
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

theorem alignment_joint_actual_terminal_translation_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (d : ℕ) (hd : 0 < d)
    (c C : ℝ) (Kbox : ℕ) (hc : 0 < c) (hC : 0 ≤ C) (hKbox : C+1 ≤ (Kbox : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (hB : ∀ ν, 0 ≤ B ν)
    {ε : ℝ} (hε : 0 < ε) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ w in atTop, ∀ x y : Fin N → ℕ,
      y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support →
      ∀ lower upper : Option κ → ℝ,
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) →
      ∀ (e : AlignmentAddingPair N i) (coordinate : Option κ) (choice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
      let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
      let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
      let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
      let delta := alignmentPairProgression q₀ w (F.modulus w) e y
      ∀ obs : C(J.G ⧸ J.Γ,ℂ), obs ∈ alignmentJointOriginalTestFamily D n v hv slots B L →
      ‖alignmentJointTranslatedDenominatorMean D n v hv r b F q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi (fun j => if j=coordinate then delta else 0) obs-
        alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi obs‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let K : ℝ := ∏ ν, B ν
  have hK : 0 ≤ K := Finset.prod_nonneg (fun ν _ => hB ν)
  let tolerance := ε*c/(8*K+1)
  have htolerance : 0 < tolerance := div_pos (mul_pos hε hc) (by positivity)
  have htoleranceEq : (8*K+1)*tolerance=ε*c := by dsimp only [tolerance]; field_simp
  filter_upwards [alignment_actual_rounded_box_geometry_eventually (ι := κ) hF i T c C Kbox hc hC hKbox,
    alignmentPairProgression_eventually_dvd hF q₀ d hq hd,
    alignmentPairProgression_scale_small hF q₀ hq i T htolerance,
    alignment_retained_scale_eventually hF i T d hd 0 (eps := c/4) (by positivity),
    master_microcell_eventually_positive hF (fun _ => i),alignmentGlobalRawMass_geometry hF]
    with w hgeom hdiv hsmall hscale hR hraw
  intro x y hy lower upper hbox e coordinate choice shift weight g a obs hobs
  have hunit := alignmentGlobalRawMass_support_coprime F w y hy
  have hp := fun j (_hj : j ∈ T) => alignmentGlobalRawMass_support_positive hF w y hy j
  have hb := hgeom y hp lower upper hbox
  dsimp only at hb
  have hZ : 0 < alignmentCubeScale F w i T y :=
    zero_lt_one.trans_le (alignmentCubeScale_ge_one F w i T y hR)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := hscale y 1 0 (by norm_num)
    (by unfold MasterParameterFamily.auxiliary; omega) (Nat.zero_le _)
  simp only [pow_zero,Nat.cast_one,mul_one] at hs
  rw [←mul_div_assoc] at hs
  have hdle := (le_div_iff₀ hdR).mp hs
  have hδ := hsmall y hunit (fun j _ => hraw.2.2 y hy j) e
  have hδd := hdiv y hunit i e
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
  let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
  let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
  have hlen : ∀ z, (c/2)*alignmentCubeScale F w i T y ≤ (hi z : ℝ)-(lo z : ℝ) := by
    intro z
    simpa only [Int.cast_sub] using (hb z).2.2.1
  have hobsbound := alignment_joint_original_test_family_norm_bound D n v hv slots B L obs hobs
  have hh := alignment_joint_terminal_single_translation_bound D n v hv r b F q₀ w T x d hd choice
    shift weight g a (fun k : T => y k.val) lo hi coordinate (alignmentPairProgression q₀ w (F.modulus w) e y)
    hδd (alignmentCubeScale F w i T y) (c/2) K (by positivity) (by nlinarith) hlen hK obs hobsbound
  apply lt_of_le_of_lt hh
  have hden : 0 < (c/2)*alignmentCubeScale F w i T y := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 4*K)
  nlinarith

end Hindman168
