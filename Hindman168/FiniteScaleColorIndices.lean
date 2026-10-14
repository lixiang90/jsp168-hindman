import Hindman168.FiniteScaleLists

/-! Every scale and color is indexed in one finite family. A chain
block product is inserted by its proved membership, not by a choice
of an approximate or externally supplied scale. -/

namespace Hindman168
open scoped Classical

abbrev ScaleColorIndex (A : Finset ℚ) (r : ℕ) := {a : ℚ // a ∈ A} × Fin r

def scaleColorFactor (A : Finset ℚ) (r : ℕ) (γ : ScaleColorIndex A r) : ℚ := γ.1.val

def scaleColorValue (A : Finset ℚ) (r : ℕ) (γ : ScaleColorIndex A r) : Fin r := γ.2

def scaleBlockColorIndex {n r : ℕ} (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (b : Fin n → ℚ) (hb : b ∈ B)
    (S : Finset (Fin n)) (hS : S.Nonempty) (color : Fin r) : ScaleColorIndex A r :=
  (⟨finiteScaleBlockProduct b S, hclosed b hb S hS⟩, color)

theorem scaleColorFactor_positive (A : Finset ℚ) (r : ℕ)
    (hA : ∀ a ∈ A, 0 < a) (γ : ScaleColorIndex A r) : 0 < scaleColorFactor A r γ :=
  hA γ.1.val γ.1.property

theorem scaleBlockColorIndex_factor {n r : ℕ} (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (b : Fin n → ℚ) (hb : b ∈ B)
    (S : Finset (Fin n)) (hS : S.Nonempty) (color : Fin r) :
    scaleColorFactor A r (scaleBlockColorIndex B A hclosed b hb S hS color) =
      finiteScaleBlockProduct b S := rfl

theorem scaleBlockColorIndex_color {n r : ℕ} (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (b : Fin n → ℚ) (hb : b ∈ B)
    (S : Finset (Fin n)) (hS : S.Nonempty) (color : Fin r) :
    scaleColorValue A r (scaleBlockColorIndex B A hclosed b hb S hS color) = color := rfl

end Hindman168
