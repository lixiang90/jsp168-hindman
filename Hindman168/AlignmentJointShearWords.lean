import Hindman168.WeightedShearAction
import Hindman168.PositivePrincipalSumMassPlanOptions
import Hindman168.AlignmentAuxiliaryWords

/-! The actual finite word action has two coordinates: a joint weighted
shear and the independent integer residue-slot translation. Terminal own
words must move BOTH coordinates; arbitrary cumulative jumps remain shears. -/
namespace Hindman168
open scoped Classical

 theorem alignment_word_value_map {n : ℕ} {i : Fin n} {G H : Type*}
    [Group G] [Group H] (p : G →* H) (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (word : List (AlignmentAddingPair n i × ℚ)) :
    p (alignmentWordValue q₀ b L word) = alignmentWordValue q₀ b (p ∘ L) word := by
  induction word with
  | nil => exact p.map_one
  | cons l word ih => simp only [alignmentWordValue, map_mul, map_zpow, ih, Function.comp_apply]

 theorem alignment_pivot_route_map {n : ℕ} {i : Fin n} {G H : Type*}
    [Group G] [Group H] (p : G →* H) (q₀ : ℕ)
    (L : AlignmentAddingPair n i → G) (plan : List (AlignmentPivotStage n i))
    (b : Fin n → ℚ) (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) :
    principalPivotRouteValue q₀ (p ∘ L) plan b route =
      ((principalPivotRouteValue q₀ L plan b route).1,
        p (principalPivotRouteValue q₀ L plan b route).2) := by
  induction plan generalizing route with
  | nil => simp [principalPivotRouteValue]
  | cons stage earlier ih =>
    cases route with
    | nil => simp [principalPivotRouteValue]
    | cons a route =>
      simp only [principalPivotRouteValue, ih, map_mul, alignment_word_value_map]

variable {σ : Type*} {n : ℕ} {i : Fin n}

abbrev AlignmentJointShearGroup (w : σ → ℕ) :=
  weightedShearGroup (R := ℝ) w × Multiplicative (AlignmentAddingPair n i → ℤ)

abbrev AlignmentJointShearState :=
  (σ → ℝ) × Multiplicative (AlignmentAddingPair n i → ℤ)

noncomputable instance alignmentJointShearAction (w : σ → ℕ) :
    MulAction (AlignmentJointShearGroup (i := i) w) (AlignmentJointShearState (σ := σ) (i := i)) where
  smul g x := (g.1 • x.1, g.2 * x.2)
  one_smul x := Prod.ext (one_smul _ _) (one_mul _)
  mul_smul g h x := Prod.ext (mul_smul g.1 h.1 x.1) (mul_assoc g.2 h.2 x.2)

noncomputable def alignmentJointShearLetter (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (e : AlignmentAddingPair n i) : AlignmentJointShearGroup (i := i) w :=
  (L e, Multiplicative.ofAdd (alignmentAuxiliaryUnit e 1))

 theorem alignment_joint_shear_group_step (w : σ → ℕ) (s : ℕ)
    (hw : ∀ j, w j ≤ s) (hs : 1 ≤ s) :
    (⊤ : Subgroup (AlignmentJointShearGroup (i := i) w)).lowerCentralSeries s = ⊥ :=
  weightedShearGroup_prod_lowerCentral_bot w s hw hs _

 theorem alignment_joint_shear_letter_slot (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (e : AlignmentAddingPair n i) (x : AlignmentJointShearState (σ := σ) (i := i))
    (f : AlignmentAddingPair n i) :
    ((alignmentJointShearLetter w L e • x).2.toAdd) f =
      x.2.toAdd f + if f = e then 1 else 0 := by
  change (alignmentAuxiliaryUnit e 1 + x.2.toAdd) f = _
  simp only [Pi.add_apply, alignmentAuxiliaryUnit]
  omega

 theorem alignment_joint_shear_word_slots (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (q₀ : ℕ) (b : Fin n → ℚ) (word : List (AlignmentAddingPair n i × ℚ))
    (x : AlignmentJointShearState (σ := σ) (i := i)) :
    (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word • x).2.toAdd =
      x.2.toAdd + alignmentAuxiliaryWord q₀ b word := by
  exact alignmentWordValue_auxiliary_translation q₀ b (alignmentJointShearLetter w L)
    (fun x : AlignmentJointShearState (σ := σ) (i := i) => x.2.toAdd)
    (alignment_joint_shear_letter_slot w L) word x

 theorem alignment_joint_shear_word_first (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (q₀ : ℕ) (b : Fin n → ℚ) (word : List (AlignmentAddingPair n i × ℚ))
    (x : AlignmentJointShearState (σ := σ) (i := i)) :
    (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word • x).1 =
      alignmentWordValue q₀ b L word • x.1 := by
  have h := alignment_word_value_map (MonoidHom.fst _ _) q₀ b
    (alignmentJointShearLetter w L) word
  change (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word).1 • x.1 = _
  change (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word).1 =
    alignmentWordValue q₀ b L word at h
  exact congrArg (fun g => g • x.1) h

end Hindman168
