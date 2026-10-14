import Hindman168.SelectedAlignmentKeyObservableTopology
import Hindman168.AlignmentArrayNativeCoordinates
import Hindman168.AlignmentAddingPairs

/-! Choose the actual models, observers and finite integer-evaluation arrays
from the original represented family, before any cofinal sequence, sample or
threshold is supplied. Quotient topology transport preserves every recipe
value and the original uniform bound and Lipschitz constant. -/
namespace Hindman168
open Module NNReal
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

theorem selected_alignment_recipe_array_models {ι : Type} {M s : ℕ}
    (i : Fin M) (F : MasterParameterFamily) (gap : ℕ → Fin M)
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ ν, NativePieceRepresented.{u} s F gap (f ν)) :
    ∃ (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
      (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M i → ℤ)
      (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
        (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
      (dim : ι → ℕ)
      (basis : ∀ ν, Basis (Fin (dim ν)) ℝ (alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)).E)
      (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
      (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G) (B : ι → ℝ) (Lip : ι → ℝ≥0),
      (∀ ν, 0 ≤ B ν) ∧
      (∀ ν w p z, |obs ν w p z| ≤ B ν) ∧
      (∀ ν w p x y, dist (obs ν w p x) (obs ν w p y) ≤
        (Lip ν : ℝ) * @dist ((D ν).G ⧸ (D ν).Γ) (D ν).metric.toDist x y) ∧
      ∀ ν, f ν = piecewiseLinearNilsequence (D ν).Γ F gap (obs ν) (g ν) (a ν) := by
  choose D hD using hf
  obtain ⟨obs,g,a,B,Lip,hB,hbound,hLip,hrecipe⟩ := alignment_native_piece_family_recipes D F gap f hD
  have harray : ∀ ν : ι, ∃ (r : ℕ) (v : Fin (r+1) → AlignmentAddingPair M i → ℤ),
      Function.Injective (alignmentNativeFiniteEvaluation
        (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) r v) :=
    fun ν => alignmentNativeFiniteEvaluation_exists_injective
      (σ := AlignmentAddingPair M i) (E := (D ν).E) (I := (D ν).I) (G := (D ν).G)
  choose r v hv using harray
  let dim := fun ν => Module.finrank ℝ (alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)).E
  let basis := fun ν => Module.finBasis ℝ (alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)).E
  refine ⟨D,r,v,hv,dim,basis,(fun ν w p => selectedAlignmentQuotientObservable (D ν) (obs ν w p)),
    g,a,B,Lip,hB,hbound,?_,?_⟩
  · intro ν w p x y
    letI := (D ν).metric
    exact (hLip ν w p).dist_le_mul x y
  · intro ν
    exact (hrecipe ν).trans
      (selected_alignment_quotient_observable_piecewise (D ν) F gap (obs ν) (g ν) (a ν)).symm

end Hindman168
