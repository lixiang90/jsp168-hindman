import Hindman168.AlignmentNativeCompleteCubeGlobal

/-! Actual native complete-test marginal face failure tends to zero for arbitrarily
width-varying, exposed-key-selected source formulae. Every positive-mass
conditioning preserves this zero limit and supplies supported original
samples satisfying ALL own faces and ALL zero/one vertex profiles. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_native_complete_cube_all_faces_global_tendsto
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (B : ℝ) (L : NNReal)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) → ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ, ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) N)
      (fun y => alignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d
        (shift w (alignmentShortExposureKey F w i T y))
        (g w (alignmentShortExposureKey F w i T y)) (a w (alignmentShortExposureKey F w i T y)) B L c C ε y)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro z hz
    filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact hz.trans_le (event_nonneg _ _ hw.1)
  · intro z hz
    have hh := alignment_native_complete_cube_all_faces_global_eventually (κ := κ) D n v hv r b
      hF q₀ hq T hT d hd c C K hc hC hK B L hε hz
    filter_upwards [hh] with w hw
    exact hw (shift w) (g w) (a w)

include n v hv r b in
theorem alignment_native_complete_cube_all_faces_positive_conditioning
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (B : ℝ) (L : NNReal)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) → ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ, ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    {ε : ℝ} (hε : 0 < ε)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ w in atTop, β ≤ event (globalRawMass (F.cutoff w) (primorial w) N) (S w)) :
    Tendsto (fun w => event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N) (S w))
      (fun y => alignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d
        (shift w (alignmentShortExposureKey F w i T y))
        (g w (alignmentShortExposureKey F w i T y)) (a w (alignmentShortExposureKey F w i T y)) B L c C ε y)) atTop (𝓝 0) := by
  apply finite_positive_conditioning_zero_limit _ _ _
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1)) hβ hS
  exact alignment_native_complete_cube_all_faces_global_tendsto (κ := κ) D n v hv r b
    hF q₀ hq T hT d hd c C K hc hC hK B L shift g a hε

include n v hv r b in
theorem alignment_native_complete_cube_all_faces_supported_selection
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (B : ℝ) (L : NNReal)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) → ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ, ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    {ε : ℝ} (hε : 0 < ε)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ w in atTop, β ≤ event (globalRawMass (F.cutoff w) (primorial w) N) (S w)) :
    ∀ᶠ w in atTop, ∃ y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      S w y ∧ ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d
        (shift w (alignmentShortExposureKey F w i T y))
        (g w (alignmentShortExposureKey F w i T y)) (a w (alignmentShortExposureKey F w i T y)) B L c C ε y := by
  have hh := (alignment_native_complete_cube_all_faces_global_tendsto (κ := κ) D n v hv r b
    hF q₀ hq T hT d hd c C K hc hC hK B L shift g a hε).eventually (gt_mem_nhds hβ)
  filter_upwards [hh,hS,alignmentGlobalRawMass_geometry hF] with w hw hs hraw
  by_contra hn
  have hmono : event (globalRawMass (F.cutoff w) (primorial w) N) (S w) ≤
      event (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d
        (shift w (alignmentShortExposureKey F w i T y))
        (g w (alignmentShortExposureKey F w i T y)) (a w (alignmentShortExposureKey F w i T y)) B L c C ε y) := by
    apply event_mono_on_support _ _ _ hraw.1
    intro y hy hsy
    by_contra hbad
    exact hn ⟨y,hy,hsy,hbad⟩
  linarith

end Hindman168
