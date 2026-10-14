import Hindman168.PositivePrincipalSumNativeIndices
import Hindman168.AlignmentIntegerArrayArguments
import Hindman168.AlignmentExposedArrayOffsets

/-! Finite simultaneous own-target native translations, with their actual
integer array arguments. Both residue and progression slots must change. -/
namespace Hindman168
open scoped BigOperators Classical

theorem alignment_integer_array_argument_own_sum {n : ℕ} {i : Fin n} {ι : Type*}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (Q : AlignmentAddingPair n i → ℕ)
    (T : Finset (Fin n)) (D : Finset ι) (pair : ι → AlignmentAddingPair n i)
    (z : ι → ℤ) (htarget : ∀ k ∈ D, (pair k).targetTail = T)
    (hexact : ∀ k ∈ D, (M : ℤ) * Δ (pair k) = (Q (pair k) : ℤ) -
      (alignmentNaturalBlockProduct t T : ℤ) * ρ (pair k))
    (p : ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T p
        (v + ∑ k ∈ D, alignmentAuxiliaryUnit (pair k) (z k))
        (u + ∑ k ∈ D, alignmentAuxiliaryUnit (pair k) (z k)) =
      alignmentIntegerArrayArgument t M ρ Δ T p v u + ∑ k ∈ D, z k * Q (pair k) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert k D hk ih =>
    have htargetD := fun j hj => htarget j (Finset.mem_insert_of_mem hj)
    have hexactD := fun j hj => hexact j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    rw [show v + (alignmentAuxiliaryUnit (pair k) (z k) +
      ∑ j ∈ D, alignmentAuxiliaryUnit (pair j) (z j)) =
      (v + ∑ j ∈ D, alignmentAuxiliaryUnit (pair j) (z j)) +
        alignmentAuxiliaryUnit (pair k) (z k) by abel]
    rw [show u + (alignmentAuxiliaryUnit (pair k) (z k) +
      ∑ j ∈ D, alignmentAuxiliaryUnit (pair j) (z j)) =
      (u + ∑ j ∈ D, alignmentAuxiliaryUnit (pair j) (z j)) +
        alignmentAuxiliaryUnit (pair k) (z k) by abel]
    rw [alignmentIntegerArrayArgument_own_letter t M ρ Δ Q T (pair k)
      (htarget k (Finset.mem_insert_self _ _)) (hexact k (Finset.mem_insert_self _ _)),
      ih htargetD hexactD]
    ring

/-- Native simultaneous own-target shifts at the selected indices give the
exact final sum-form input, with no event-equivalence hypothesis. -/
theorem principal_native_array_argument_sum
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (T : Finset (Fin n)) (i : Fin n) (hbefore : ∀ k ∈ T, k < i)
    (D : Finset (AlignmentAddingPair n i)) (htarget : ∀ p ∈ D, p.targetTail = T)
    (b : Fin n → ℚ) (hb : ∀ k, 0 < b k) (z : AlignmentAddingPair n i → ℤ)
    (hz : ∀ p ∈ D, (z p : ℚ) = (q₀ : ℚ) *
      (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)))
    (hratio : ∀ p ∈ D,
      ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
        (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w /
        principalBlockCoefficient M e p.targetTail i
        (finiteScaleBlockProduct b (alignmentPairTargetBlock p)) w : ℕ) : ℚ) =
      ((selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairSourceBlock p)) /
      ((selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairTargetBlock p))) :
    let f := principalAlignmentEmbedding e heM
    let rho := fun p : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) p x
    let delta := fun p : AlignmentAddingPair M (f i) => alignmentPairProgression q₀ w (F.modulus w) p x
    let slots := ∑ p ∈ D, alignmentAuxiliaryUnit (p.map f) (z p)
    alignmentIntegerArrayArgument x (F.modulus w) rho delta (T.image f) (x (f i)) slots slots =
      (principalSubsetProduct (insert i T) (fun k => x (f k)) : ℤ) +
      ∑ p ∈ D,
        ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
          (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w /
          principalBlockCoefficient M e T i
          (finiteScaleBlockProduct b (insert i T)) w : ℕ) : ℤ) *
          principalSubsetProduct (alignmentPairSourceBlock p) (fun k => x (f k)) := by
  dsimp only
  let f := principalAlignmentEmbedding e heM
  let rho := fun p : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) p x
  let delta := fun p : AlignmentAddingPair M (f i) => alignmentPairProgression q₀ w (F.modulus w) p x
  have ht (p) (hp : p ∈ D) : (p.map f).targetTail = T.image f := by
    simp only [AlignmentAddingPair.map, htarget p hp]
  have he (p) (hp : p ∈ D) : (F.modulus w : ℤ) * delta (p.map f) =
      (alignmentIntegerNumerator q₀ w (p.map f) x : ℤ) -
        (alignmentNaturalBlockProduct x (T.image f) : ℤ) * rho (p.map f) := by
    simpa only [ht p hp] using alignmentPairProgression_exact hF hq hw x hx (p.map f)
  have h := alignment_integer_array_argument_own_sum x (F.modulus w) rho delta
    (fun p => alignmentIntegerNumerator q₀ w p x) (T.image f) D (fun p => p.map f) z ht he
    (x (f i)) 0 0
  simp only [zero_add] at h
  rw [h]
  congr 1
  · have hi : i ∉ T := fun hi => (lt_irrefl i) (hbefore i hi)
    simp only [alignmentIntegerArrayArgument, alignmentIntegerSlotShift_zero,
      alignmentIntegerArrayProgression, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      ite_self, mul_zero, add_zero, alignment_natural_block_product_image,
      principalSubsetProduct, Finset.prod_insert hi, Nat.cast_mul]
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro p hp
    have hs := principal_alignment_native_letter_shift e heM hq hw p x b hb (z p)
      (hz p hp) (hratio p hp)
    simpa only [alignmentPairTargetBlock, htarget p hp, f, principalAlignmentEmbedding,
      OrderEmbedding.coe_ofStrictMono] using hs

end Hindman168
