import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Nonzero polynomial zero sets under atomless product measures

The leading-coefficient exceptional set is handled by induction. Only
outside it is a fiber treated as a nonzero one-variable polynomial.
The result applies to genuine sigma-finite coordinate measures, with
zero singleton masses, over a topological integral domain.
-/

namespace Hindman168

open MeasureTheory Filter
open scoped Topology Classical

theorem polynomial_roots_measure_zero {R : Type*} [CommRing R] [IsDomain R]
    [MeasurableSpace R] (μ : Measure R) [NullSingletonClass μ]
    (p : Polynomial R) (hp : p ≠ 0) : μ {x | p.eval x = 0} = 0 := by
  have heq : {x | p.eval x = 0} = (p.roots.toFinset : Set R) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  rw [heq]
  exact p.roots.toFinset.measure_zero μ

theorem mvPolynomial_zero_set_measurable {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R] {n : ℕ} (p : MvPolynomial (Fin n) R) :
    MeasurableSet {x | MvPolynomial.eval x p = 0} :=
  (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet

theorem mvPolynomial_zero_set_measure_zero {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R] :
    ∀ {n : ℕ} (μ : Fin n → Measure R) [∀ i, SigmaFinite (μ i)]
      [∀ i, NullSingletonClass (μ i)] {p : MvPolynomial (Fin n) R},
      p ≠ 0 → (Measure.pi μ) {x | MvPolynomial.eval x p = 0} = 0
  | 0, μ, _, _, p, hp => by
    rw [p.eq_C_of_isEmpty] at hp ⊢
    have hc := MvPolynomial.C_ne_zero.mp hp
    simp [hc]
  | n + 1, μ, _, _, p, hp => by
    let p' := MvPolynomial.finSuccEquiv R n p
    let q := p'.leadingCoeff
    have hp' : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hp
    have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
    let ν := Measure.pi (fun i : Fin n => μ i.succ)
    have hqnull : ν {x | MvPolynomial.eval x q = 0} = 0 :=
      mvPolynomial_zero_set_measure_zero (fun i => μ i.succ) hq
    have hae : ∀ᵐ x ∂ν, MvPolynomial.eval x q ≠ 0 :=
      measure_eq_zero_iff_ae_notMem.mp hqnull
    let S : Set (R × (Fin n → R)) := {y | MvPolynomial.eval (Fin.cons y.1 y.2) p = 0}
    have hs : MeasurableSet S := by
      apply IsClosed.measurableSet
      exact isClosed_eq ((MvPolynomial.continuous_eval p).comp (by fun_prop)) continuous_const
    have hSnull : ((μ 0).prod ν) S = 0 := by
      rw [Measure.prod_apply_symm hs]
      calc
        _ = ∫⁻ _x, (0 : ENNReal) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hae] with x hx
          let r := p'.map (MvPolynomial.eval x)
          have hr : r ≠ 0 := by
            intro hz
            have hc := congrArg (fun f : Polynomial R => f.coeff p'.natDegree) hz
            simp only [r, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
            exact hx (by simpa only [q, Polynomial.leadingCoeff] using hc)
          have heq : (fun a => (a, x)) ⁻¹' S = {a | r.eval a = 0} := by
            ext a
            simp only [S, Set.mem_preimage, Set.mem_setOf_eq, MvPolynomial.eval_eq_eval_mv_eval']
            rfl
          rw [heq]
          exact polynomial_roots_measure_zero (μ 0) r hr
        _ = 0 := by simp
    have hpres := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
    have hpres' : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => R) 0)
        (Measure.pi μ) ((μ 0).prod ν) := by simpa only [Fin.succAbove_zero] using hpres
    have h := hpres'.measure_preimage hs.nullMeasurableSet
    have heq : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => R) 0) ⁻¹' S =
        {x | MvPolynomial.eval x p = 0} := by
      ext x
      simp [S, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.cons_self_tail]
    rw [heq] at h
    simpa only [Fin.succAbove_zero] using h.trans hSnull

end Hindman168
