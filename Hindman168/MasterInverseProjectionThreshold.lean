import Hindman168.MasterIntervalInverseProjection

namespace Hindman168
open FiniteMass Filter NNReal
open scoped BigOperators Topology Classical
universe u v

/-- With the displayed positive finite-list interval inverse conclusion,
a sufficiently small actual fine projection forces the actual global
Gowers norm below delta on an ultrafilter-large set of stages. -/
theorem MasterParameterConditions.interval_inverse_projection_norm_threshold
    {n N : ℕ} {A : Finset ℚ} {polys : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A polys F) (s : ℕ) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (h : boundedHilbertFamilies (fun w =>
      FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
    (hf : ∀ w y, |h.val w y| ≤ 1)
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
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
            (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖)
    (hprojection :
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
        (hilbertFamilyToCompletion _ U h)‖ < δ ^ (2 ^ d) / 2 * γ) :
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
    ∀ᶠ w in (U : Filter ℕ),
      weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) (p w) d (f w) < δ := by
  intro q C mass p f
  letI : ∀ w, NeZero (q w) := fun w =>
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  by_contra hn
  have hbad := Ultrafilter.eventually_not.mpr hn
  have hglobal : ∀ᶠ w in (U : Filter ℕ),
      δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod (q w))) (p w) d (f w) :=
    hbad.mono (fun _ hw => le_of_not_gt hw)
  have hlower := hF.interval_inverse_projection_lower s U hU gap pivot horder h hf
    D Lip d hd δ γ hδ hγ.le hinterval hglobal
  exact (not_lt_of_ge hlower) hprojection

end Hindman168
