import Hindman168.AlignmentNativeWindowUniform
import Hindman168.ActualSelectorUniformity

/-! Remove dependence of the eventual cutoff on a chosen raw anchor sequence.
Positive actual typical-event mass supplies genuine anchors at every large
width. Uniformity covers ALL supported typical anchors and retained subsets. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical
universe u

def AlignmentNativeWindowCap {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ) {n : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (x : Fin n → ℕ) (U : Finset (Fin n)) (j : T) (denominator : ℕ)
    (Kref K c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ index : ι, ∀ (q : ℕ) (a : Fin m → ℤ), 0 < q →
    ∀ (Q : (Option (Fin m) → ℝ) → (D index).G)
      (pN : RoughVectorMvPolynomial (Option (Fin m)) (D index).E),
    RoughVectorMvDegreeLE pN degree →
    (∀ (z : ℝ) (y : Fin m → ℝ), roughVectorMvEval pN (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D index).E) (I := (D index).I)
        (roughNativeResidualSource (D index) Q a q (Option.elim · z y))) →
    ∀ Zactual : ℕ → ℝ,
    (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val),
      alignmentCubeScale F w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref) ≤ Zactual t ∧
      Zactual t ≤ K*(alignmentCubeScale F w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref))) →
    event (uniformFinsetMass
      (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
      (fun t => RoughNativeRealResidualComplexLargeIndex (D index) Q a q t t
        (Zactual t) c C L B η) < δ

theorem alignment_native_window_all_anchors_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentTypicalShortPosterior F w i T x → ∀ U : Finset (Fin n), U ⊆ T →
      ∀ j : T, AlignmentNativeWindowCap D m degree F w i T x U j
        denominator Kref K c C B η δ L := by
  by_cases hTnon : T.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hTnon
    let V : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T) → Prop := fun w a =>
      a.1 ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      alignmentTypicalShortPosterior F w i T a.1 ∧ a.2.1 ⊆ T
    let Good : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T) → Prop := fun w a =>
      AlignmentNativeWindowCap D m degree F w i T a.1 a.2.1 a.2.2
        denominator Kref K c C B η δ L
    have hV : ∀ᶠ w in atTop, ∃ a, V w a := by
      filter_upwards [alignmentGlobalRawMass_geometry hF,
        (alignment_typicalShortPosterior_success_tendsto hF i T).eventually
          (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hg ht
      obtain ⟨x,hx,hgood⟩ := exists_supported_of_event_pos _ _ hg.1 ht
      exact ⟨(x,∅,⟨j₀,hj₀⟩),hx,hgood,Finset.empty_subset T⟩
    have hselectors (a : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T))
        (ha : ∀ᶠ w in atTop, V w (a w)) : ∀ᶠ w in atTop, Good w (a w) := by
      exact alignment_native_actual_window_uniform D m degree hF i T hT denominator
        hdenominator Kref K c C B η L hKref hK hc hC hB hη
        (fun w => (a w).1) (fun w => (a w).2.1) (fun w => (a w).2.2) ha hδ
    have hh := rough_eventual_uniform_of_actual_selectors
      ((fun _ => 0),∅,⟨j₀,hj₀⟩) V Good hV hselectors
    filter_upwards [hh] with w hw
    intro x hx ht U hU j
    exact hw (x,U,j) ⟨hx,ht,hU⟩
  · filter_upwards [] with w
    intro x hx ht U hU j
    exact (hTnon ⟨j.val,j.property⟩).elim

end Hindman168
