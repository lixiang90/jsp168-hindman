import Hindman168.IntegerIntervalGowersZeroExtension
import Hindman168.FiniteComplexMean

/-! The genuine one-dimensional interval identity, including empty intervals.
No positive denominator is assumed when the interval is empty: both sides
are zero by the existing totalised finite-mean definitions. -/

namespace Hindman168
open scoped BigOperators Classical

/-- An interval one-cube is exactly an ordered pair of interval points. -/
noncomputable def integerIntervalCubeOneEquiv (L : ℕ) :
    ↥(integerIntervalCubeDomain 1 L) ≃ (Fin L × Fin L) where
  toFun p :=
    (⟨p.val.1.toNat, by
      have h := (mem_integerIntervalCubeDomain p.val).mp p.property ∅
      simp only [integerCubeVertex, Finset.sum_empty, add_zero] at h
      omega⟩,
     ⟨(p.val.1 + p.val.2 0).toNat, by
      have h := (mem_integerIntervalCubeDomain p.val).mp p.property {0}
      simp only [integerCubeVertex, Finset.sum_singleton] at h
      omega⟩)
  invFun p := ⟨((p.1.val : ℤ), fun _ => (p.2.val : ℤ) - p.1.val), by
    apply (mem_integerIntervalCubeDomain _).mpr
    intro ω
    have hcases : ω = ∅ ∨ ω = {0} := by
      have : ω ∈ ({∅, {0}} : Finset (Finset (Fin 1))) := by
        have he : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
        rw [← he]
        exact Finset.mem_univ _
      simpa using this
    rcases hcases with rfl | rfl
    · simp only [integerCubeVertex, Finset.sum_empty, add_zero]
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast p.1.isLt⟩
    · simp only [integerCubeVertex, Finset.sum_singleton, add_sub_cancel]
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast p.2.isLt⟩⟩
  left_inv p := by
    apply Subtype.ext
    have h0 := (mem_integerIntervalCubeDomain p.val).mp p.property ∅
    have h1 := (mem_integerIntervalCubeDomain p.val).mp p.property {0}
    simp only [integerCubeVertex, Finset.sum_empty, add_zero] at h0
    simp only [integerCubeVertex, Finset.sum_singleton] at h1
    apply Prod.ext
    · exact Int.toNat_of_nonneg h0.1
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change ((p.val.1 + p.val.2 0).toNat : ℤ) - (p.val.1.toNat : ℤ) = p.val.2 0
      rw [Int.toNat_of_nonneg h1.1, Int.toNat_of_nonneg h0.1]
      omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext
    · simp
    · simp

theorem integerPeriodicCubeProduct_one_dimension (q : ℕ) (v : ZMod q → ℝ)
    (p : ℤ × (Fin 1 → ℤ)) :
    integerPeriodicCubeProduct q 1 v p = v (p.1 : ZMod q) * v (p.1 + p.2 0 : ℤ) := by
  have he : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [integerPeriodicCubeProduct, he, integerCubeVertex]

/-- Exact interval cube-power identity, valid also at length zero. -/
theorem integerIntervalPeriodicCubeMean_one_dimension (q L : ℕ) (v : ZMod q → ℝ) :
    integerIntervalPeriodicCubeMean q 1 L v =
      (finiteHaarMean (fun n : Fin L => v (n.val : ZMod q))) ^ 2 := by
  have hc : (integerIntervalCubeDomain 1 L).card = L * L := by
    simpa using Fintype.card_congr (integerIntervalCubeOneEquiv L)
  have hs : (∑ p ∈ integerIntervalCubeDomain 1 L, integerPeriodicCubeProduct q 1 v p) =
      (∑ n : Fin L, v (n.val : ZMod q)) ^ 2 := by
    rw [← Finset.sum_coe_sort (integerIntervalCubeDomain 1 L) (integerPeriodicCubeProduct q 1 v)]
    calc
      _ = ∑ p : Fin L × Fin L, v (p.1.val : ZMod q) * v (p.2.val : ZMod q) := by
        apply Fintype.sum_equiv (integerIntervalCubeOneEquiv L)
        intro p
        have h0 := (mem_integerIntervalCubeDomain p.val).mp p.property ∅
        have h1 := (mem_integerIntervalCubeDomain p.val).mp p.property {0}
        simp only [integerCubeVertex, Finset.sum_empty, add_zero] at h0
        simp only [integerCubeVertex, Finset.sum_singleton] at h1
        rw [integerPeriodicCubeProduct_one_dimension]
        change v (p.val.1 : ZMod q) * v (p.val.1 + p.val.2 0 : ℤ) =
          v (p.val.1.toNat : ZMod q) * v ((p.val.1 + p.val.2 0).toNat : ZMod q)
        congr 1 <;> congr 1
        · simpa only [Int.cast_natCast] using
            (congrArg (fun z : ℤ => (z : ZMod q)) (Int.toNat_of_nonneg h0.1)).symm
        · simpa only [Int.cast_natCast] using
            (congrArg (fun z : ℤ => (z : ZMod q)) (Int.toNat_of_nonneg h1.1)).symm
      _ = _ := by
        simp only [Fintype.sum_prod_type, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact mul_comm _ _
  rw [integerIntervalPeriodicCubeMean, hs, hc]
  simp only [finiteHaarMean, Fintype.card_fin, Nat.cast_mul, pow_two, div_mul_div_comm]

/-- In dimension one the actual interval Gowers value is precisely the
absolute mean. This includes the empty interval without cancellation. -/
theorem integerIntervalPeriodicGowersValue_one_dimension (q L : ℕ) (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q 1 L v =
      |finiteHaarMean (fun n : Fin L => v (n.val : ZMod q))| := by
  have hm : 0 ≤ integerIntervalPeriodicCubeMean q 1 L v := by
    rw [integerIntervalPeriodicCubeMean_one_dimension]
    exact sq_nonneg _
  have hp := integerIntervalPeriodicGowersValue_pow q 1 L v hm
  have hg := integerIntervalPeriodicGowersValue_nonneg q 1 L v hm
  have he : integerIntervalPeriodicGowersValue q 1 L v ^ 2 =
      |finiteHaarMean (fun n : Fin L => v (n.val : ZMod q))| ^ 2 := by
    simpa only [pow_one, integerIntervalPeriodicCubeMean_one_dimension, sq_abs] using hp
  nlinarith [abs_nonneg (finiteHaarMean (fun n : Fin L => v (n.val : ZMod q)))]

/-- The same identity in the complex correlation convention of the native
inverse interface. -/
theorem integerIntervalPeriodicGowersValue_one_eq_complexMean_norm
    (q L : ℕ) (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q 1 L v =
      ‖finiteComplexMean (fun n : Fin L => (v (n.val : ZMod q) : ℂ))‖ := by
  rw [integerIntervalPeriodicGowersValue_one_dimension]
  have he : finiteComplexMean (fun n : Fin L => (v (n.val : ZMod q) : ℂ)) =
      (finiteHaarMean (fun n : Fin L => v (n.val : ZMod q)) : ℂ) := by
    simp [finiteComplexMean, finiteHaarMean]
  rw [he, Complex.norm_real, Real.norm_eq_abs]

end Hindman168
