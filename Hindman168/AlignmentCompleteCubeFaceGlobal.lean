import Hindman168.AlignmentCompleteCubeFacePosterior
import Hindman168.AlignmentTypicalPosteriorKeys
import Hindman168.FiniteTypicalExposureEventBound

/-! Actual ORIGINAL raw law has vanishing marginal face failure, uniformly
before every exposed-key-selected original source formula. The exact original
posterior disintegration integrates all typical keys, and actual bad-key mass
vanishes. Source choices may vary with the key, but not with unexposed factors. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_complete_cube_all_faces_global_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ℝ) (L : NNReal)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ (shift : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) → ι → AlignmentAddingPair N i → ℤ)
      (g a : ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G),
      event (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentCompleteCubeAllFacesFailure (κ := κ) D F q₀ w T d
          (shift (alignmentShortExposureKey F w i T y)) slots
          (g (alignmentShortExposureKey F w i T y)) (a (alignmentShortExposureKey F w i T y)) B L c C ε y) < δ := by
  have hδ' : 0 < δ/2 := by positivity
  have hh := alignment_complete_cube_all_faces_posterior_vanishing (κ := κ) D n v hv r b
    hF q₀ hq T hT d hd c C K hc hC hK slots B L hε hδ'
  have hbad := (alignment_typicalShortPosterior_failure_tendsto hF i T).eventually (gt_mem_nhds hδ')
  filter_upwards [hh,hbad,alignmentGlobalRawMass_geometry hF] with w hw hbadw hraw
  intro shift g a
  let μ := globalRawMass (F.cutoff w) (primorial w) N
  let key := alignmentShortExposureKey F w i T
  let Good := alignmentShortPosteriorKeyGood F w i T
  let E : (Fin N → ℕ) → Prop := fun y => alignmentCompleteCubeAllFacesFailure (κ := κ) D F q₀ w T d
    (shift (key y)) slots (g (key y)) (a (key y)) B L c C ε y
  have hcap : ∀ x ∈ μ.support, Good (key x) →
      event (conditionMass μ (fun y => key y=key x)) E ≤ δ/2 := by
    intro x hx hg
    have htyp := (alignmentShortPosteriorKeyGood_key F w i T x).mp hg
    have hc' := hw x hx htyp (shift (key x)) (g (key x)) (a (key x))
    have heq : event (conditionMass μ (fun y => key y=key x)) E=
        event (conditionMass μ (fun y => key y=key x))
          (alignmentCompleteCubeAllFacesFailure (κ := κ) D F q₀ w T d
            (shift (key x)) slots (g (key x)) (a (key x)) B L c C ε) := by
      apply event_congr_on_support
      intro y hy
      have hkey : key y=key x := by
        by_contra hn
        have hnz := Finsupp.mem_support_iff.mp hy
        rw [conditionMass_apply,if_neg hn] at hnz
        exact hnz rfl
      dsimp only [E]
      rw [hkey]
    rw [heq]
    exact hc'.le
  have hh' := finite_typical_exposure_event_bound μ key Good E hraw.1 hδ'.le hcap
  have hb : event μ (fun y => ¬ Good (key y)) < δ/2 := by
    simpa only [Good,key,μ,alignmentShortPosteriorKeyGood_key] using hbadw
  rw [hraw.2.1,mul_one] at hh'
  change event μ E < δ
  linarith

end Hindman168
