import Hindman168.PositivePrincipalSumAlignment
import Hindman168.FiniteScaleColorIndices
import Hindman168.MasterChainColumnRatios

/-!
# Exact original rational ratios in the adding-pair event

The normalized integer ratios used by `PrincipalAddingAlignment` agree
with the rational scale ratios in (2.12) at all sufficiently late stages.
No rounding or altered alignment condition is used in the final proof.
-/

namespace Hindman168
open Filter
open scoped BigOperators Classical

noncomputable def principalChainOfAddingPair {n : ℕ} {i : Fin n}
    (p : AlignmentAddingPair n i) : PrincipalCoordinateChain n 2 where
  tail := ![p.sourceTail, p.targetTail]
  pivot := ![p.sourcePivot, i]
  tail_nonempty := by intro k; fin_cases k <;> simp [p.source_nonempty, p.target_nonempty]
  tail_before := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
    exact p.source_before_target
  tails_before_pivots := by
    have hs : ∀ k ∈ p.sourceTail, k < p.sourcePivot := by
      intro k hk
      obtain ⟨j, hj⟩ := p.target_nonempty
      exact (p.source_before_target k hk j hj).trans (p.target_before_sourcePivot j hj)
    intro k l
    fin_cases k <;> fin_cases l
    · simpa using hs
    · exact fun k hk => (hs k hk).trans p.sourcePivot_before
    · simpa using p.target_before_sourcePivot
    · exact fun k hk => (p.target_before_sourcePivot k hk).trans p.sourcePivot_before
  pivot_strictMono := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
    exact p.sourcePivot_before

/-- Every adding pair has the exact source/target coefficient ratio of
(2.12); the natural quotient introduces no rounding. -/
theorem MasterParameterConditions.principal_adding_ratios_exact_eventually
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A) :
    ∀ᶠ w in atTop, ∀ b ∈ B, ∀ i : Fin n, ∀ p : AlignmentAddingPair n i,
      let cs := principalBlockCoefficient M e p.sourceTail p.sourcePivot
        (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w
      let ct := principalBlockCoefficient M e p.targetTail i
        (finiteScaleBlockProduct b (alignmentPairTargetBlock p)) w
      0 < cs ∧ 0 < ct ∧ ct ∣ cs ∧
        ((cs / ct : ℕ) : ℚ) =
          ((selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
              finiteScaleBlockProduct b (alignmentPairSourceBlock p)) /
          ((selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
              finiteScaleBlockProduct b (alignmentPairTargetBlock p)) := by
  filter_upwards [hF.coefficients, hF.chain_ratios] with w hw hr
  have hblock (T : Finset (Fin n)) (i : Fin n) (a : ℚ) (ha : a ∈ A) :
      0 < principalBlockCoefficient M e T i a w ∧
      (selectedSubsetScale M e w (insert i T) : ℚ) * a =
        principalBlockCoefficient M e T i a w := by
    obtain ⟨c, hc, he, _⟩ := hw a ha ((insert i T).image (energyPrincipal e))
      (selectedPrincipal_image_range e heM _) ((Finset.insert_nonempty _ _).image _)
    have hs : (selectedSubsetScale M e w (insert i T) : ℚ) * a = c := by
      rw [selectedSubsetScale_eq_master e heM]
      exact he
    have hf : principalBlockCoefficient M e T i a w = c := by
      simp only [principalBlockCoefficient, hs, Nat.floor_natCast]
    exact ⟨hf ▸ hc, hf.symm ▸ hs⟩
  intro b hb i p cs ct
  have has := hclosed b hb (alignmentPairSourceBlock p) (Finset.insert_nonempty _ _)
  have hat := hclosed b hb (alignmentPairTargetBlock p) (Finset.insert_nonempty _ _)
  have hs := hblock p.sourceTail p.sourcePivot _ has
  have ht := hblock p.targetTail i _ hat
  have hseq : (selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
      finiteScaleBlockProduct b (alignmentPairSourceBlock p) = cs := hs.2
  have hteq : (selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
      finiteScaleBlockProduct b (alignmentPairTargetBlock p) = ct := ht.2
  let C := principalChainOfAddingPair p
  obtain ⟨t, htRatio⟩ := hr _ has _ hat 2 (C.lift e) (C.lift_range e heM) 0 1 (by decide)
  rw [C.lift_block e 0, C.lift_block e 1,
    ← selectedSubsetScale_eq_master e heM, ← selectedSubsetScale_eq_master e heM] at htRatio
  have hratio : (cs : ℚ) / ct = (primorial w : ℚ) * t := by
    change ((selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
      finiteScaleBlockProduct b (alignmentPairSourceBlock p)) /
      ((selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
      finiteScaleBlockProduct b (alignmentPairTargetBlock p)) = _ at htRatio
    rw [hseq, hteq] at htRatio
    exact htRatio
  have hd : ct ∣ cs := (naturalRatio_W_divisible ht.1 hratio).1
  refine ⟨hs.1, ht.1, hd, ?_⟩
  rw [Nat.cast_div hd (by exact_mod_cast (Nat.ne_of_gt ht.1))]
  rw [hseq, hteq]

end Hindman168
