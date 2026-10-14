import Hindman168.SelectedAlignmentFaceCompleteGlobal

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
theorem selected_alignment_native_complete_cube_all_faces_global_tendsto
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (B : ℝ) (L : NNReal)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) → ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ, ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) N)
      (fun y => selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv (alignmentGeometryWithGap F i gap) gap q₀ w T d
        (shift w (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y))
        (g w (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) (a w (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) B L c C ε y)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro z hz
    filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact hz.trans_le (event_nonneg _ _ hw.1)
  · intro z hz
    have hh := selected_alignment_native_complete_cube_all_faces_global_eventually (κ := κ) D n v hv r b
      hF gap hgap q₀ hq T hT d hd c C K hc hC hK B L hε hz
    filter_upwards [hh] with w hw
    exact hw (shift w) (g w) (a w)

end Hindman168
