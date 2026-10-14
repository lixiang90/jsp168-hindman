import Hindman168.FinalStrongFromNativeInverse
import Lean
open Hindman168
open scoped BigOperators Classical
universe u
set_option pp.universes true
set_option pp.explicit true in
#check @Hindman168.strongConjecture_of_native_inverse
set_option pp.explicit true in
#check @Hindman168.finiteConjecture_of_native_inverse
set_option pp.explicit true in
#check @Hindman168.hasUniformSelectedPrincipalAlignment
#print Hindman168.StrongConjecture
#print Hindman168.StrongWitness
#print Hindman168.FiniteConjecture
#print Hindman168.MonoFSFP
#print Hindman168.HasUniformSelectedPrincipalAlignment
#print Hindman168.HasNativePeriodicIntervalInverse
#print axioms Hindman168.strongConjecture_of_native_inverse
#print axioms Hindman168.finiteConjecture_of_native_inverse
#print axioms Hindman168.hasUniformSelectedPrincipalAlignment
#print axioms Hindman168.finite_iff_strong
#print axioms Hindman168.maskGeneratedMaster_conditions
#print axioms Hindman168.finite_scale_prediction_models_unit_observables
#print axioms Hindman168.principal_final_deduction_tolerances
#print axioms Hindman168.MasterParameterConditions.principal_positive_sum_yields_finite_witness

example : (∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t - 1) t) →
    StrongConjecture := strongConjecture_of_native_inverse
example : HasUniformSelectedPrincipalAlignment.{u} := hasUniformSelectedPrincipalAlignment

-- An actual coloring prevents the zero-color branch from proving a positive-color case.
example {r : ℕ} (χ : ℕ → Fin r) : 0 < r := by
  have h := (χ 0).isLt
  omega

-- Zero target size is a legitimate additional boundary case, with an actual color.
example {r : ℕ} (χ : ℕ → Fin r) (R D : ℝ) : StrongWitness (m := 0) χ R D := by
  refine ⟨Fin.elim0, ?_, ?_, ?_, χ 0, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro S hS
    obtain ⟨i, _⟩ := hS
    exact Fin.elim0 i

-- A paper-style split between a₁>R and the later-index inequality.
def PaperSplitWitness {r m : ℕ} (χ : ℕ → Fin r) (R D : ℝ) : Prop :=
  ∃ a : Fin (m+1) → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ R < (a 0 : ℝ) ∧
    (∀ i : Fin (m+1), 0 < i.val →
      R * ((∑ j ∈ Finset.univ.filter (fun j : Fin (m+1) => j < i), (a j : ℝ)) +
      (∏ j ∈ Finset.univ.filter (fun j : Fin (m+1) => j < i), (a j : ℝ))) ^ D < (a i : ℝ)) ∧
    ∃ c : Fin r, ∀ S : Finset (Fin (m+1)), S.Nonempty →
      χ (∑ i ∈ S, a i) = c ∧ χ (∏ i ∈ S, a i) = c

theorem strongWitness_iff_paperSplit {r m : ℕ} (χ : ℕ → Fin r) (R D : ℝ) :
    StrongWitness (m := m+1) χ R D ↔ PaperSplitWitness (m := m) χ R D := by
  constructor
  · rintro ⟨a, hs, hp, hg, c, hc⟩
    refine ⟨a, hs, hp, ?_, fun i _ => hg i, c, hc⟩
    simpa using hg 0
  · rintro ⟨a, hs, hp, hfirst, hrest, c, hc⟩
    refine ⟨a, hs, hp, ?_, c, hc⟩
    intro i
    by_cases hi : i = 0
    · subst i
      simpa using hfirst
    · apply hrest i
      have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega

-- Singletons are covered by the exact common-color predicate.
example {r m : ℕ} (χ : ℕ → Fin r) (a : Fin m → ℕ) (c : Fin r)
    (h : ∀ S : Finset (Fin m), S.Nonempty →
      χ (∑ i ∈ S, a i) = c ∧ χ (∏ i ∈ S, a i) = c) (i : Fin m) : χ (a i) = c := by
  simpa using (h {i} (by simp)).1

-- K=0 does not activate the positive-threshold inverse premise.
example (q d : ℕ) (v : ZMod q → ℝ) : integerIntervalPeriodicGowersValue q d 0 v = 0 := by
  have hdom : integerIntervalCubeDomain d 0 = ∅ := by simp [integerIntervalCubeDomain]
  simp only [integerIntervalPeriodicGowersValue, integerIntervalPeriodicCubeMean, hdom,
    Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
  exact Real.zero_rpow (by positivity)

#print axioms strongWitness_iff_paperSplit

-- No positive-size product chain can hide in n=0 or n=1.
example {n m : ℕ} (C : PrincipalCoordinateChain n (m+1)) : 2 ≤ n := by
  obtain ⟨j, hj⟩ := C.tail_nonempty 0
  have hbefore := C.tails_before_pivots 0 0 j hj
  have hlt := (C.pivot 0).isLt
  have hbefore' : j.val < (C.pivot 0).val := hbefore
  omega

-- Scale closure together with a real index and nonempty B forces A nonempty.
example {n : ℕ} (hn : 0 < n) (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hB : B.Nonempty) (hclosed : FiniteScaleClosure B A) : A.Nonempty := by
  obtain ⟨b, hb⟩ := hB
  exact ⟨finiteScaleBlockProduct b {⟨0,hn⟩}, hclosed b hb {⟨0,hn⟩} (by simp)⟩

-- The empty alignment schedule has mass budget exactly one, not zero.
example (r s : ℕ) : selectedAlignmentScheduleDelta 0 r s = 1 := by
  simp [selectedAlignmentScheduleDelta, principalPivotDelta]

-- With n=0 the event is genuinely the full sample space because B is nonempty.
example {r M : ℕ} (e : Fin (2*0) ↪o ℕ) (B : Finset (Fin 0 → ℚ))
    (A : Finset ℚ) (hclosed : FiniteScaleClosure B A) (hB : B.Nonempty)
    (S : Finset (Fin 0) → Fin 0 → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (w : ℕ) (x : Fin 0 → ℕ) : PrincipalSumAlignmentEvent M e B A hclosed S θ w x := by
  obtain ⟨b, hb⟩ := hB
  refine ⟨⟨b,hb⟩, ?_⟩
  intro κ T i
  exact Fin.elim0 i
