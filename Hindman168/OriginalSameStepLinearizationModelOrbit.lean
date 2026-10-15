import Hindman168.OriginalSameStepLinearizationGeometry
import Hindman168.OriginalSameStepLinearizationRealOrbit

/-! The fixed lattice absorbs the integer clock. This is equality in the
actual left-coset quotient, for all integer times and arbitrary real
polynomial coefficients. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)

noncomputable def clockDirection : TimeTorus.Algebra 1 :=
  fun _ => ((fixedGridData D hs).clock : ℚ)

/-- The chosen clock generator really belongs to the real ambient lattice. -/
theorem realClock_mem :
    realTimeInclusion D.filtration hs 1 (Multiplicative.ofAdd (clockDirection D hs)) ∈
      (ambientModel D hs).realLattice := by
  apply Subgroup.mem_map.mpr
  refine ⟨timeInclusion D.filtration hs 1 (Multiplicative.ofAdd (clockDirection D hs)), ?_, rfl⟩
  have heq : timeInclusion D.filtration hs 1 (Multiplicative.ofAdd (clockDirection D hs)) =
      (⟨((fixedGridData D hs).clock : ℚ) • unitTime D⟩ : Group D.filtration hs 1) := by
    apply NilpotentLieBCHGroup.ext
    apply LieAlgebra.SemiDirectSum.ext
    · simp [unitTime, timeInclusion]
    · change (fun _ : Fin 1 => ((fixedGridData D hs).clock : ℚ)) =
        (fun _ : Fin 1 => ((fixedGridData D hs).clock : ℚ) * 1)
      funext i
      exact (mul_one _).symm
  rw [heq]
  exact (fixedGridData D hs).clock_mem

theorem realClock_zsmul_mem (n : ℤ) :
    realTimeInclusion D.filtration hs 1 (Multiplicative.ofAdd (n • clockDirection D hs)) ∈
      (ambientModel D hs).realLattice := by
  have heq : Multiplicative.ofAdd (n • clockDirection D hs) =
      (Multiplicative.ofAdd (clockDirection D hs)) ^ n := by
    apply Multiplicative.toAdd.injective
    simp
  rw [heq, map_zpow]
  exact (ambientModel D hs).realLattice.zpow_mem (realClock_mem D hs) n

/-- Every real polynomial on the original geometry has an exact linear orbit
    in this one fixed same-step model. The right coset correction is a genuine
    lattice element; it is not assumed to vanish in a formal quotient. -/
theorem exists_linear_orbit_fiber
    (p : RealAdaptedGroup D.filtration (fun _ : Fin 1 => 1)) :
    ∃ (g x : (ambientModel D hs).RealGroup)
      (u : ℤ → (fiberModel D hs).RealGroup),
      (∀ n, realFiberEvaluation D.filtration 1 0 (u n) =
        realAdaptedEvaluation D.filtration (fun _ : Fin 1 => (n : ℚ)) p) ∧
      ∀ n, (QuotientGroup.mk (g ^ n * x) : (ambientModel D hs).Space) =
        QuotientGroup.mk (modelFiberInclusion D hs (u n)) := by
  let A := (fixedGridData D hs).clock
  have hA : (A : ℚ) ≠ 0 := by exact_mod_cast (fixedGridData D hs).clock_pos.ne'
  let h := clockDirection D hs
  let q := realAdaptedDilation D.filtration (A : ℚ)⁻¹ p
  let a := realPolynomialStep D.filtration 1 h q
  let b := realPolynomialBasepoint D.filtration 1 h q
  let lift := realIntegerSemidirectLift D.filtration hs 1 h
  refine ⟨lift a, lift b, fun n => ((a ^ n) * b).left, ?_, ?_⟩
  · intro n
    rw [realPolynomial_readout]
    change realAdaptedEvaluation D.filtration (n • h)
      (realAdaptedDilation D.filtration (A : ℚ)⁻¹ p) = _
    rw [realAdaptedEvaluation_dilation]
    apply congrArg (fun x : Fin 1 → ℚ => realAdaptedEvaluation D.filtration x p)
    funext i
    change (A : ℚ)⁻¹ * ((n : ℚ) * (A : ℚ)) = (n : ℚ)
    field_simp [hA]
  · intro n
    rw [← map_zpow, ← map_mul]
    change (QuotientGroup.mk
      (realIntegerSemidirectLift D.filtration hs 1 h ((a ^ n) * b)) :
      (ambientModel D hs).Space) = _
    rw [realIntegerSemidirectLift_apply]
    apply QuotientGroup.mk_mul_of_mem
    change realTimeInclusion D.filtration hs 1
      (Multiplicative.ofAdd (((a ^ n) * b).right.toAdd • h)) ∈ _
    rw [realPolynomial_clock]
    exact realClock_zsmul_mem D hs n

end Hindman168.OriginalSameStepLinearization
