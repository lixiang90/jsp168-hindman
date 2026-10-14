import Hindman168.CyclicIntervalNativeCorrelators
import Hindman168.MasterRawPeriodCellProjection

namespace Hindman168
open FiniteMass Filter NNReal
open scoped BigOperators Topology Classical
universe u v

/-- The displayed finite-list interval inverse conclusion at threshold
delta/4 implies the paper's fine projection lower bound on the actual
master harmonic law. All cyclic transfer, period extraction, native
family synthesis and actual-law integration are proved in this chain.
The interval inverse conclusion itself remains an explicit input. -/
theorem MasterParameterConditions.interval_inverse_projection_lower
    {n N : ℕ} {A : Finset ℚ} {polys : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A polys F) (s : ℕ) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (h : boundedHilbertFamilies (fun w =>
      FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
    (hf : ∀ w y, |h.val w y| ≤ 1)
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (hinterval : ∀ (q : ℕ) [NeZero q] (K : ℕ) (v : ZMod q → ℝ),
      (∀ z, |v z| ≤ 1) →
      δ / 4 ≤ integerIntervalPeriodicGowersValue q d (K * q) v →
      ∃ i : ι,
        letI := (D i).metric
        letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
          (D i).metric.toUniformSpace.toTopologicalSpace
        ∃ (obs : C((D i).G ⧸ (D i).Γ, ℂ)) (g x : (D i).G),
          (∀ z, ‖obs z‖ ≤ 1) ∧ LipschitzWith (Lip i) obs ∧
          γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
            (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖) :
    let q := fun w => F.gap w (gap w).val / (F.modulus w : ℕ)
    letI : ∀ w, NeZero (q w) := fun w => ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
    let C := fun w => masterCompleteCells F gap pivot w
    let mass := fun w (c : C w) => ∑ y ∈ intervalResidueSet
      (c.val.1 * ((F.modulus w : ℕ) * q w : ℕ)) ((F.modulus w : ℕ) * q w)
      (F.modulus w : ℕ) c.val.2.val, integerMass (F.cutoff w (pivot w).val) (primorial w) y
    let p := fun w (c : C w) => mass w c / ∑ a, mass w a
    let f := fun w (c : C w) (z : ZMod (q w)) =>
      h.val w (c.val.1 * ((F.modulus w : ℕ) * q w : ℕ) + c.val.2.val +
        ((F.modulus w : ℕ) : ℤ) * z.val)
    (∀ᶠ w in (U : Filter ℕ),
      δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) (p w) d (f w)) →
    δ ^ (2 ^ d) / 2 * γ ≤
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ := by
  intro q C mass p f hglobal
  letI : ∀ w, NeZero (q w) := fun w =>
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  have hhalf : 0 < δ / 2 := by positivity
  have hinv : ∀ (q : ℕ) [NeZero q] (K : ℕ) (v : ZMod q → ℝ),
      (∀ z, |v z| ≤ 1) →
      (δ / 2) / 2 ≤ integerIntervalPeriodicGowersValue q d (K * q) v →
      ∃ i : ι,
        letI := (D i).metric
        letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
          (D i).metric.toUniformSpace.toTopologicalSpace
        ∃ (obs : C((D i).G ⧸ (D i).Γ, ℂ)) (g x : (D i).G),
          (∀ z, ‖obs z‖ ≤ 1) ∧ LipschitzWith (Lip i) obs ∧
          γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
            (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖ := by
    have he : (δ / 2) / 2 = δ / 4 := by ring
    simpa only [he] using hinterval
  obtain ⟨K, hK, hcells⟩ := native_interval_inverse_to_cell_correlators D Lip d hd
    (δ / 2) γ hhalf hinv
  apply hF.raw_period_correlator_projection_lower s U hU gap pivot horder h hf D Lip K hK
    d hd δ γ hδ.le hγ hglobal
  exact Eventually.of_forall (fun w c hc => hcells (F.modulus w : ℕ) (q w)
    c.val.1 c.val.2 (fun y => h.val w y) (hf w) hc)

end Hindman168
