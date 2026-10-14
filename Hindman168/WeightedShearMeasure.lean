import Hindman168.WeightedShearAction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Algebra.MvPolynomial.Variables

/-!
Volume preservation of genuine weighted polynomial shears.  The proof splits
coordinates by weight and uses conditional translation invariance of product
Lebesgue measure.  It does not assume a Jacobian or a measure-preserving lift.
-/

namespace Hindman168
open MvPolynomial MeasureTheory

/-- Continuous triangular changes of coordinates preserve finite product Lebesgue measure.
There is no bound on dimension or the sizes of the displacement functions. -/
theorem weightedTriangular_measurePreserving (s : ℕ) :
    ∀ {σ : Type*} [Fintype σ] (w : σ → ℕ) (_hw : ∀ i, w i ≤ s)
      (p : σ → (σ → ℝ) → ℝ),
      (∀ i, Continuous (p i)) →
      (∀ i x y, (∀ j, w j < w i → x j = y j) → p i x = p i y) →
      MeasurePreserving (fun x : σ → ℝ => fun i => x i+p i x) := by
  classical
  induction s with
  | zero =>
      intro σ _ w hw p hp hdep
      have heq : (fun x : σ → ℝ => fun i => x i+p i x) =
          fun x => x+(fun i => p i 0) := by
        funext x i
        congr 1
        apply hdep i x 0
        intro j hj
        have hi := hw i
        omega
      rw [heq]
      exact measurePreserving_add_right volume _
  | succ s ih =>
      intro σ _ w hw p hp hdep
      let L := {i : σ // w i ≤ s}
      let U := {i : σ // ¬w i ≤ s}
      let e : (σ → ℝ) ≃ᵐ ((L → ℝ) × (U → ℝ)) :=
        MeasurableEquiv.piEquivPiSubtypeProd (fun _ : σ => ℝ) (fun i => w i ≤ s)
      let fill : (L → ℝ) → (σ → ℝ) := fun x => e.symm (x,0)
      have hfill : Continuous fill := by
        apply continuous_pi
        intro i
        by_cases hi : w i ≤ s
        · change Continuous (fun x : L → ℝ => if h : w i ≤ s then x ⟨i,h⟩ else 0)
          simpa only [dif_pos hi] using (continuous_apply (⟨i,hi⟩ : L))
        · change Continuous (fun x : L → ℝ => if h : w i ≤ s then x ⟨i,h⟩ else 0)
          simp only [dif_neg hi]
          exact continuous_const
      have hfill_eq (x : L → ℝ) (i : σ) (hi : w i ≤ s) : fill x i = x ⟨i,hi⟩ := by
        change (if h : w i ≤ s then x ⟨i,h⟩ else 0) = _
        simp only [dif_pos hi]
      let pL : L → (L → ℝ) → ℝ := fun i x => p i.val (fill x)
      have hlow : MeasurePreserving (fun x : L → ℝ => fun i => x i+pL i x) := by
        apply ih (fun i : L => w i.val) (fun i => i.property) pL
        · intro i
          exact (hp i.val).comp hfill
        · intro i x y hxy
          apply hdep i.val (fill x) (fill y)
          intro j hj
          have hjL : w j ≤ s := (Nat.le_of_lt hj).trans i.property
          rw [hfill_eq x j hjL, hfill_eq y j hjL]
          exact hxy ⟨j,hjL⟩ hj
      let shift : (L → ℝ) → (U → ℝ) := fun x i => p i.val (fill x)
      have hshift : Continuous shift := by
        apply continuous_pi
        intro i
        exact (hp i.val).comp hfill
      have hskew : MeasurePreserving
          (fun z : (L → ℝ) × (U → ℝ) =>
            ((fun i => z.1 i+pL i z.1), z.2+shift z.1)) := by
        change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
        apply hlow.skew_product (μc := volume) (μd := volume) (g := fun x y => y+shift x)
        · exact (continuous_snd.add (hshift.comp continuous_fst)).measurable
        · exact Filter.Eventually.of_forall fun x => (measurePreserving_add_right volume (shift x)).map_eq
      have he : MeasurePreserving e :=
        volume_preserving_piEquivPiSubtypeProd (fun _ : σ => ℝ) (fun i => w i ≤ s)
      have hall := (he.symm e).comp (hskew.comp he)
      have hpfill (i : σ) (x : σ → ℝ) : p i x = p i (fill (e x).1) := by
        apply hdep i x (fill (e x).1)
        intro j hj
        have hjL : w j ≤ s := by have := hw i; omega
        rw [hfill_eq (e x).1 j hjL]
        rfl
      have hmap : (fun x : σ → ℝ => fun i => x i+p i x) =
          e.symm ∘ (fun z : (L → ℝ) × (U → ℝ) =>
            ((fun i => z.1 i+pL i z.1), z.2+shift z.1)) ∘ e := by
        funext x i
        by_cases hi : w i ≤ s
        · change x i+p i x =
            (if h : w i ≤ s then (e x).1 ⟨i,h⟩+pL ⟨i,h⟩ (e x).1
              else (e x).2 ⟨i,h⟩+shift (e x).1 ⟨i,h⟩)
          simp only [dif_pos hi]
          exact congrArg (fun r => x i+r) (hpfill i x)
        · change x i+p i x =
            (if h : w i ≤ s then (e x).1 ⟨i,h⟩+pL ⟨i,h⟩ (e x).1
              else (e x).2 ⟨i,h⟩+shift (e x).1 ⟨i,h⟩)
          simp only [dif_neg hi]
          exact congrArg (fun r => x i+r) (hpfill i x)
      rw [hmap]
      exact hall

/-- A polynomial of degree below `j` uses only variables of weight below `j`. -/
theorem weightedShear_eval_depends_lower {σ : Type*} (w : σ → ℕ)
    (p : MvPolynomial σ ℝ) (j : ℕ)
    (hp : p ∈ weightedShearDegreeLE w ((j : ℤ)-1)) (x y : σ → ℝ)
    (hxy : ∀ i, w i < j → x i = y i) : MvPolynomial.eval x p = MvPolynomial.eval y p := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro i hi _
  apply hxy i
  obtain ⟨a, ha, hia⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hw := Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hia)
  have hd := hp a ha
  omega

/-- Every actual weighted polynomial shear preserves Lebesgue measure. -/
theorem weightedShearMap_measurePreserving {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (p : σ → MvPolynomial σ ℝ)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)) :
    MeasurePreserving (fun x : σ → ℝ => fun i => x i+MvPolynomial.eval x (p i)) := by
  apply weightedTriangular_measurePreserving s w hw (fun i x => MvPolynomial.eval x (p i))
  · intro i
    exact MvPolynomial.continuous_eval (p i)
  · intro i x y hxy
    exact weightedShear_eval_depends_lower w (p i) (w i) (hp i) x y hxy

/-- Every word in the common nilpotent shear group preserves the same cover volume. -/
theorem weightedShearPoint_measurePreserving {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (f : weightedShearGroup (R := ℝ) w) :
    MeasurePreserving (fun x : σ → ℝ => f • x) := by
  obtain ⟨p, hp, haction⟩ := weightedShearPoint_displacements w f
  have heq : (fun x : σ → ℝ => f • x) =
      fun x : σ → ℝ => fun i => x i+MvPolynomial.eval x (p i) := by
    funext x i
    exact haction x i
  rw [heq]
  exact weightedShearMap_measurePreserving w s hw p hp

end Hindman168
