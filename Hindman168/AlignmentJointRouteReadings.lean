import Hindman168.AlignmentJointShearWords

/-! Own-letter equivariance is propagated through both signs of integer
powers and the original ordered words. The final stored factor is fixed
throughout the proof; no equivariance for intermediate stored factors or
commutation of the actual shear letters is used. -/
namespace Hindman168
open scoped Classical

/-- A reading equivariance, unlike an additive scalar cocycle, shifts its
query parameter. Both signs of the group power are included. -/
theorem alignment_reading_integer_power {G X A Y : Type*}
    [Group G] [MulAction G X] [AddCommGroup A]
    (read : A → X → Y) (g : G) (t : A)
    (hstep : ∀ u x, read u (g • x) = read (u+t) x)
    (z : ℤ) (u : A) (x : X) :
    read u (g ^ z • x) = read (u + z • t) x := by
  have hinv : ∀ u x, read u (g⁻¹ • x) = read (u-t) x := by
    intro u x
    have h := hstep (u-t) (g⁻¹ • x)
    simpa only [smul_inv_smul, sub_add_cancel] using h.symm
  induction z using Int.induction_on generalizing u x with
  | zero => simp only [zpow_zero, one_smul, zero_smul, add_zero]
  | succ n ih =>
    rw [zpow_add, zpow_one, mul_smul, ih, hstep]
    congr 1
    rw [add_zsmul, one_zsmul]
    abel
  | pred n ih =>
    rw [zpow_sub, zpow_one, mul_smul, ih, hinv]
    congr 1
    rw [sub_zsmul, one_zsmul]
    abel

theorem alignment_auxiliary_unit_zsmul {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) (z : ℤ) :
    z • alignmentAuxiliaryUnit e 1 = alignmentAuxiliaryUnit e z := by
  funext f
  simp only [Pi.smul_apply, alignmentAuxiliaryUnit, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The order of actual noncommuting letters is retained. Only their query
increments are added in the commutative integer-slot space. -/
theorem alignment_reading_ordered_word {n : ℕ} {i : Fin n} {G X Y : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G)
    (read : (AlignmentAddingPair n i → ℤ) → X → Y)
    (word : List (AlignmentAddingPair n i × ℚ))
    (hstep : ∀ l ∈ word, ∀ u x,
      read u (L l.1 • x) = read (u + alignmentAuxiliaryUnit l.1 1) x)
    (u : AlignmentAddingPair n i → ℤ) (x : X) :
    read u (alignmentWordValue q₀ b L word • x) =
      read (u + alignmentAuxiliaryWord q₀ b word) x := by
  induction word generalizing u with
  | nil => simp only [alignmentWordValue, one_smul, alignmentAuxiliaryWord, add_zero]
  | cons l word ih =>
    rw [alignmentWordValue, mul_smul,
      alignment_reading_integer_power read (L l.1) (alignmentAuxiliaryUnit l.1 1)
        (hstep l List.mem_cons_self), alignment_auxiliary_unit_zsmul,
      ih (fun a ha => hstep a (List.mem_cons_of_mem l ha))]
    simp only [alignmentAuxiliaryWord, add_assoc]

/-- Actual simultaneous shear/slot action. Fixing the final stored factor
v+m is sufficient for the reading R_(v,0) to become R_(v+m,m). -/
theorem alignment_joint_terminal_word_reading
    {σ Y Z : Type*} {n : ℕ} {i : Fin n} (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (projection : (σ → ℝ) → Y)
    (read : (AlignmentAddingPair n i → ℤ) → (AlignmentAddingPair n i → ℤ) → Y → Z)
    (q₀ : ℕ) (b : Fin n → ℚ) (word : List (AlignmentAddingPair n i × ℚ))
    (x : AlignmentJointShearState (σ := σ) (i := i))
    (hstep : ∀ l ∈ word, ∀ u z,
      read (x.2.toAdd + alignmentAuxiliaryWord q₀ b word) u (projection (L l.1 • z)) =
        read (x.2.toAdd + alignmentAuxiliaryWord q₀ b word)
          (u + alignmentAuxiliaryUnit l.1 1) (projection z)) :
    read (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word • x).2.toAdd 0
        (projection (alignmentWordValue q₀ b (alignmentJointShearLetter w L) word • x).1) =
      read (x.2.toAdd + alignmentAuxiliaryWord q₀ b word)
        (alignmentAuxiliaryWord q₀ b word) (projection x.1) := by
  rw [alignment_joint_shear_word_slots, alignment_joint_shear_word_first]
  simpa only [zero_add] using alignment_reading_ordered_word q₀ b L
    (fun u z => read (x.2.toAdd + alignmentAuxiliaryWord q₀ b word) u (projection z))
    word hstep 0 x.1

/-- Route arithmetic is defined without any native coset or selected lift. -/
noncomputable def alignmentJointRouteArithmetic {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) :
    (Fin n → ℚ) × Multiplicative (AlignmentAddingPair n i → ℤ) :=
  principalPivotRouteValue q₀
    (fun e => Multiplicative.ofAdd (alignmentAuxiliaryUnit e 1)) plan b route

/-- In particular both final scales and the stored slot label are independent
of the arbitrary native lift chosen for each letter. -/
theorem alignment_joint_route_arithmetic {σ : Type*} {n : ℕ} {i : Fin n}
    (w : σ → ℕ) (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) :
    alignmentJointRouteArithmetic q₀ plan b route =
      ((principalPivotRouteValue q₀ (alignmentJointShearLetter w L) plan b route).1,
        (principalPivotRouteValue q₀ (alignmentJointShearLetter w L) plan b route).2.2) := by
  exact alignment_pivot_route_map (MonoidHom.snd _ _) q₀
    (alignmentJointShearLetter w L) plan b route

end Hindman168
