import Hindman168.NativePieceRecipes
import Hindman168.SelectedPrincipalMicrocellGrowth
import Hindman168.AlignmentOriginalJointRealSource

/-! A data-only view separates the model gap from the raw pivot cutoff.
It preserves every arithmetic scale and the original joint orbit. No
`MasterParameterConditions` instance for the modified data is asserted. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

noncomputable def alignmentGeometryWithGap (F : MasterParameterFamily)
    (pivot gap : ℕ) : MasterParameterFamily :=
  { F with gap := fun w j => if j = pivot then F.gap w gap else F.gap w j }

@[simp] theorem alignmentGeometryWithGap_modulus (F : MasterParameterFamily) (pivot gap w : ℕ) :
    (alignmentGeometryWithGap F pivot gap).modulus w = F.modulus w := rfl

@[simp] theorem alignmentGeometryWithGap_cutoff (F : MasterParameterFamily) (pivot gap w j : ℕ) :
    (alignmentGeometryWithGap F pivot gap).cutoff w j = F.cutoff w j := rfl

@[simp] theorem alignmentGeometryWithGap_gap (F : MasterParameterFamily) (pivot gap w : ℕ) :
    (alignmentGeometryWithGap F pivot gap).gap w pivot = F.gap w gap := by
  simp [alignmentGeometryWithGap]

@[simp] theorem alignmentGeometryWithGap_auxiliary (F : MasterParameterFamily)
    (pivot gap w j : ℕ) :
    (alignmentGeometryWithGap F pivot gap).auxiliary w j = F.auxiliary w j := rfl

theorem alignmentGeometryWithGap_piecewise {G : Type*} [Group G]
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (pivot gap : Fin N)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G) :
    piecewiseLinearNilsequence Γ (alignmentGeometryWithGap F pivot gap) (fun _ => pivot)
      obs g x = piecewiseLinearNilsequence Γ F (fun _ => gap) obs g x := by
  funext w y
  simp only [piecewiseLinearNilsequence, alignmentGeometryWithGap_gap,
    alignmentGeometryWithGap_modulus]

theorem alignmentGeometryWithGap_nativePieceOn {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (pivot gap : Fin N) (f : ℕ → ℤ → ℝ) :
    nativePieceOn D (alignmentGeometryWithGap F pivot gap) (fun _ => pivot) f ↔
      nativePieceOn D F (fun _ => gap) f := by
  letI := D.metric
  unfold nativePieceOn IsBoundedPieceNilsequence
  simp only [alignmentGeometryWithGap_piecewise]

theorem alignmentGeometryWithGap_nativeRepresented {s N : ℕ}
    (F : MasterParameterFamily) (pivot gap : Fin N) (f : ℕ → ℤ → ℝ) :
    NativePieceRepresented.{u} s (alignmentGeometryWithGap F pivot gap) (fun _ => pivot) f ↔
      NativePieceRepresented.{u} s F (fun _ => gap) f := by
  simp only [NativePieceRepresented, alignmentGeometryWithGap_nativePieceOn]

theorem alignmentGeometryWithGap_localLength {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (i : Fin n) (p : Fin M) (hp : p.val = energyPrincipal e i)
    (w : ℕ) :
    alignmentLocalLength (alignmentGeometryWithGap F (energyPrincipal e i)
      (energyPadding e i)) w p = selectedPrincipalMicrocellLength F e w i := by
  simp only [alignmentLocalLength, selectedPrincipalMicrocellLength, hp,
    alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus]

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignmentGeometryWithGap_pointOrbit (F : MasterParameterFamily) (pivot gap q₀ w : ℕ)
    (T : ι → Finset (Fin N)) (y : Fin N → ℕ) (p : ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    alignmentOriginalJointPointOrbit D n v hv (alignmentGeometryWithGap F pivot gap)
      q₀ w T y p shift g a ell =
      alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell := rfl

theorem alignmentGeometryWithGap_realSource (F : MasterParameterFamily) (pivot gap q₀ w : ℕ)
    (T : ι → Finset (Fin N)) (y : Fin N → ℕ) (p : ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) (t : ℝ) :
    alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F pivot gap)
      q₀ w T y p shift g a t =
      alignmentOriginalJointRealSource D n v hv F q₀ w T y p shift g a t := rfl

end Hindman168
