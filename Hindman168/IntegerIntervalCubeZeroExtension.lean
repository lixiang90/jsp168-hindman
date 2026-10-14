import Hindman168.IntegerIntervalPeriodicMean
import Hindman168.SubgroupCubePositive

/-! Exact lifting of cyclic cubes contained in a short interval.

The no-wrap condition is `2 * (L - 1) < M`, not an exponential-in-dimension
bound. All assertions below concern actual cubes; no inverse theorem is
assumed. -/

namespace Hindman168
open scoped BigOperators Classical

/-- A vertex of a cyclic cube, with its actual cyclic increments. -/
def cyclicIntervalCubeVertex {M d : ℕ} (p : ZMod M × (Fin d → ZMod M))
    (ω : Finset (Fin d)) : ZMod M :=
  p.1 + ∑ j ∈ ω, p.2 j

/-- Reduction of the base and every signed increment. -/
def integerIntervalCubeReduction (M : ℕ) {d : ℕ}
    (p : ℤ × (Fin d → ℤ)) : ZMod M × (Fin d → ZMod M) :=
  ((p.1 : ZMod M), fun j => (p.2 j : ZMod M))

/-- Lift the base and its neighbours, then take their signed differences. -/
def cyclicIntervalCubeLift {M d : ℕ} (p : ZMod M × (Fin d → ZMod M)) :
    ℤ × (Fin d → ℤ) :=
  ((p.1.val : ℤ), fun j => ((p.1 + p.2 j).val : ℤ) - p.1.val)

theorem cyclicIntervalCubeVertex_reduction {M d : ℕ}
    (p : ℤ × (Fin d → ℤ)) (ω : Finset (Fin d)) :
    cyclicIntervalCubeVertex (integerIntervalCubeReduction M p) ω =
      (integerCubeVertex p ω : ZMod M) := by
  simp [cyclicIntervalCubeVertex, integerIntervalCubeReduction, integerCubeVertex]

/-- The two opposite sums lie in `[0, 2(L-1)]`, so congruence modulo
`M > 2(L-1)` is equality. This is the no-wrap step. -/
theorem cyclicIntervalCubeVertex_val_insert {M d L : ℕ} [NeZero M]
    (hM : 2 * (L - 1) < M) (p : ZMod M × (Fin d → ZMod M))
    (hp : ∀ ω, (cyclicIntervalCubeVertex p ω).val < L)
    (ω : Finset (Fin d)) (j : Fin d) (hj : j ∉ ω) :
    (cyclicIntervalCubeVertex p (insert j ω)).val + p.1.val =
      (cyclicIntervalCubeVertex p ω).val + (p.1 + p.2 j).val := by
  have hbase : p.1.val < L := by simpa [cyclicIntervalCubeVertex] using hp ∅
  have hsingle : (p.1 + p.2 j).val < L := by
    simpa [cyclicIntervalCubeVertex] using hp {j}
  have ha : (cyclicIntervalCubeVertex p (insert j ω)).val + p.1.val < M := by
    have := hp (insert j ω)
    omega
  have hb : (cyclicIntervalCubeVertex p ω).val + (p.1 + p.2 j).val < M := by
    have := hp ω
    omega
  have he : (((cyclicIntervalCubeVertex p (insert j ω)).val + p.1.val : ℕ) : ZMod M) =
      (((cyclicIntervalCubeVertex p ω).val + (p.1 + p.2 j).val : ℕ) : ZMod M) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    simp only [cyclicIntervalCubeVertex, Finset.sum_insert hj]
    abel
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

/-- Every vertex of the signed lift is exactly the canonical representative
of the corresponding cyclic vertex. -/
theorem integerCubeVertex_cyclicIntervalCubeLift {M d L : ℕ} [NeZero M]
    (hM : 2 * (L - 1) < M) (p : ZMod M × (Fin d → ZMod M))
    (hp : ∀ ω, (cyclicIntervalCubeVertex p ω).val < L)
    (ω : Finset (Fin d)) :
    integerCubeVertex (cyclicIntervalCubeLift p) ω =
      ((cyclicIntervalCubeVertex p ω).val : ℤ) := by
  induction ω using Finset.induction_on with
  | empty => simp [integerCubeVertex, cyclicIntervalCubeLift, cyclicIntervalCubeVertex]
  | @insert j ω hj ih =>
    have hn := cyclicIntervalCubeVertex_val_insert hM p hp ω j hj
    have hz : ((cyclicIntervalCubeVertex p (insert j ω)).val : ℤ) + p.1.val =
        ((cyclicIntervalCubeVertex p ω).val : ℤ) + (p.1 + p.2 j).val := by
      exact_mod_cast hn
    simp only [integerCubeVertex, Finset.sum_insert hj]
    change (p.1.val : ℤ) +
      (((p.1 + p.2 j).val : ℤ) - p.1.val +
        ∑ k ∈ ω, (((p.1 + p.2 k).val : ℤ) - p.1.val)) = _
    change (p.1.val : ℤ) +
      (∑ k ∈ ω, (((p.1 + p.2 k).val : ℤ) - p.1.val)) = _ at ih
    linarith

theorem cyclicIntervalCubeLift_mem {M d L : ℕ} [NeZero M]
    (hM : 2 * (L - 1) < M) (p : ZMod M × (Fin d → ZMod M))
    (hp : ∀ ω, (cyclicIntervalCubeVertex p ω).val < L) :
    cyclicIntervalCubeLift p ∈ integerIntervalCubeDomain d L := by
  apply (mem_integerIntervalCubeDomain _).mpr
  intro ω
  rw [integerCubeVertex_cyclicIntervalCubeLift hM p hp ω]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast hp ω⟩

theorem integerIntervalCubeReduction_lift {M d : ℕ} [NeZero M]
    (p : ZMod M × (Fin d → ZMod M)) :
    integerIntervalCubeReduction M (cyclicIntervalCubeLift p) = p := by
  apply Prod.ext
  · simp [integerIntervalCubeReduction, cyclicIntervalCubeLift]
  · funext j
    simp [integerIntervalCubeReduction, cyclicIntervalCubeLift]

/-- Canonical representatives recover an integer lying in the interval. -/
theorem integerIntervalCube_vertex_val {M d L : ℕ} [NeZero M] (hLM : L ≤ M)
    (p : ℤ × (Fin d → ℤ)) (hp : p ∈ integerIntervalCubeDomain d L)
    (ω : Finset (Fin d)) :
    ((cyclicIntervalCubeVertex (integerIntervalCubeReduction M p) ω).val : ℤ) =
      integerCubeVertex p ω := by
  rw [cyclicIntervalCubeVertex_reduction, ZMod.val_intCast]
  have hv := (mem_integerIntervalCubeDomain p).mp hp ω
  exact Int.emod_eq_of_lt hv.1 (hv.2.trans_le (by exact_mod_cast hLM))

theorem cyclicIntervalCubeLift_reduction {M d L : ℕ} [NeZero M] (hLM : L ≤ M)
    (p : ℤ × (Fin d → ℤ)) (hp : p ∈ integerIntervalCubeDomain d L) :
    cyclicIntervalCubeLift (integerIntervalCubeReduction M p) = p := by
  have hbase := integerIntervalCube_vertex_val hLM p hp ∅
  have hsingle (j : Fin d) := integerIntervalCube_vertex_val hLM p hp {j}
  simp only [cyclicIntervalCubeVertex, integerCubeVertex, Finset.sum_empty,
    add_zero, integerIntervalCubeReduction] at hbase
  apply Prod.ext
  · exact hbase
  · funext j
    have hj := hsingle j
    simp only [cyclicIntervalCubeVertex, integerCubeVertex, Finset.sum_singleton,
      integerIntervalCubeReduction] at hj
    change (((p.1 : ZMod M) + (p.2 j : ZMod M)).val : ℤ) -
      ((p.1 : ZMod M).val : ℤ) = p.2 j
    linarith

/-- Actual cyclic cubes all of whose vertices lie in the interval. -/
noncomputable def cyclicIntervalCubeDomain (M d L : ℕ) [NeZero M] :
    Finset (ZMod M × (Fin d → ZMod M)) :=
  Finset.univ.filter (fun p => ∀ ω, (cyclicIntervalCubeVertex p ω).val < L)

@[simp] theorem mem_cyclicIntervalCubeDomain {M d L : ℕ} [NeZero M]
    (p : ZMod M × (Fin d → ZMod M)) :
    p ∈ cyclicIntervalCubeDomain M d L ↔
      ∀ ω, (cyclicIntervalCubeVertex p ω).val < L := by
  simp [cyclicIntervalCubeDomain]

/-- A genuine bijection, preserving every vertex, between interval cubes
and the support of the zero-extended cyclic cube product. -/
noncomputable def integerCyclicIntervalCubeEquiv {M d L : ℕ} [NeZero M]
    (hL : 0 < L) (hM : 2 * (L - 1) < M) :
    ↥(integerIntervalCubeDomain d L) ≃ ↥(cyclicIntervalCubeDomain M d L) where
  toFun p := ⟨integerIntervalCubeReduction M p.val, by
    apply (mem_cyclicIntervalCubeDomain _).mpr
    intro ω
    have hLM : L ≤ M := by omega
    have he := integerIntervalCube_vertex_val hLM p.val p.property ω
    have hb := ((mem_integerIntervalCubeDomain p.val).mp p.property ω).2
    have : ((cyclicIntervalCubeVertex (integerIntervalCubeReduction M p.val) ω).val : ℤ) < L := by
      rw [he]
      exact hb
    exact_mod_cast this⟩
  invFun p := ⟨cyclicIntervalCubeLift p.val,
    cyclicIntervalCubeLift_mem hM p.val ((mem_cyclicIntervalCubeDomain _).mp p.property)⟩
  left_inv p := Subtype.ext (cyclicIntervalCubeLift_reduction (by omega) p.val p.property)
  right_inv p := Subtype.ext (integerIntervalCubeReduction_lift p.val)

/-- Extend the interval restriction of a periodic real input by zero into
a larger cyclic group. The input period `q` and ambient modulus `M` differ. -/
noncomputable def intervalPeriodicZeroExtension (q M L : ℕ) (v : ZMod q → ℝ)
    (z : ZMod M) : ℝ :=
  if z.val < L then v (z.val : ZMod q) else 0

theorem intervalPeriodicZeroExtension_cube_on_domain {q M d L : ℕ} [NeZero M]
    (hLM : L ≤ M) (v : ZMod q → ℝ)
    (p : ℤ × (Fin d → ℤ)) (hp : p ∈ integerIntervalCubeDomain d L) :
    (∏ ω : Finset (Fin d), intervalPeriodicZeroExtension q M L v
      (cyclicIntervalCubeVertex (integerIntervalCubeReduction M p) ω)) =
        integerPeriodicCubeProduct q d v p := by
  apply Finset.prod_congr rfl
  intro ω _
  have he := integerIntervalCube_vertex_val hLM p hp ω
  have hb := ((mem_integerIntervalCubeDomain p).mp hp ω).2
  have hval : (cyclicIntervalCubeVertex (integerIntervalCubeReduction M p) ω).val < L := by
    exact_mod_cast (show ((cyclicIntervalCubeVertex (integerIntervalCubeReduction M p) ω).val : ℤ) < L by
      rw [he]
      exact hb)
  rw [intervalPeriodicZeroExtension, if_pos hval]
  change v _ = v _
  congr 1
  have hc := congrArg (fun n : ℤ => (n : ZMod q)) he
  simpa only [Int.cast_natCast] using hc

theorem intervalPeriodicZeroExtension_cube_outside {q M d L : ℕ} [NeZero M]
    (v : ZMod q → ℝ) (p : ZMod M × (Fin d → ZMod M))
    (hp : p ∉ cyclicIntervalCubeDomain M d L) :
    (∏ ω : Finset (Fin d), intervalPeriodicZeroExtension q M L v
      (cyclicIntervalCubeVertex p ω)) = 0 := by
  have hn : ¬ ∀ ω, (cyclicIntervalCubeVertex p ω).val < L := by
    simpa only [mem_cyclicIntervalCubeDomain] using hp
  obtain ⟨ω, hω⟩ := not_forall.mp hn
  apply Finset.prod_eq_zero (Finset.mem_univ ω)
  simp only [intervalPeriodicZeroExtension, if_neg hω]

/-- Exact equality of unnormalised cube sums under zero extension. -/
theorem intervalPeriodicZeroExtension_cube_sum {q M d L : ℕ} [NeZero M]
    (hL : 0 < L) (hM : 2 * (L - 1) < M) (v : ZMod q → ℝ) :
    (∑ p : ZMod M × (Fin d → ZMod M),
      ∏ ω : Finset (Fin d), intervalPeriodicZeroExtension q M L v
        (cyclicIntervalCubeVertex p ω)) =
      ∑ p ∈ integerIntervalCubeDomain d L, integerPeriodicCubeProduct q d v p := by
  let F := fun p : ZMod M × (Fin d → ZMod M) =>
    ∏ ω : Finset (Fin d), intervalPeriodicZeroExtension q M L v
      (cyclicIntervalCubeVertex p ω)
  have hrestrict : ∑ p, F p = ∑ p ∈ cyclicIntervalCubeDomain M d L, F p := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    exact intervalPeriodicZeroExtension_cube_outside v p hp
  change ∑ p, F p = _
  rw [hrestrict, ← Finset.sum_coe_sort (cyclicIntervalCubeDomain M d L) F,
    ← Finset.sum_coe_sort (integerIntervalCubeDomain d L) (integerPeriodicCubeProduct q d v)]
  symm
  apply Fintype.sum_equiv (integerCyclicIntervalCubeEquiv hL hM)
  intro p
  exact (intervalPeriodicZeroExtension_cube_on_domain (by omega) v p.val p.property).symm

/-- Cyclic cube averaging has the ambient parameter count as denominator;
zero extension has not yet normalised by the number of interval cubes. -/
theorem intervalPeriodicZeroExtension_cube_average {q M d L : ℕ} [NeZero M]
    (hL : 0 < L) (hM : 2 * (L - 1) < M) (v : ZMod q → ℝ) :
    subgroupCubeAverage (⊤ : AddSubgroup (ZMod M)) d
      (intervalPeriodicZeroExtension q M L v) =
      (∑ p ∈ integerIntervalCubeDomain d L, integerPeriodicCubeProduct q d v p) /
        Fintype.card (ZMod M × (Fin d → ZMod M)) := by
  rw [← finiteCubeParameterMean_eq_top_cube, finiteHaarMean]
  change (∑ p : ZMod M × (Fin d → ZMod M),
    ∏ ω : Finset (Fin d), intervalPeriodicZeroExtension q M L v
      (cyclicIntervalCubeVertex p ω)) / _ = _
  rw [intervalPeriodicZeroExtension_cube_sum hL hM]

/-- Exact standard interval normalisation: divide the zero-extended cyclic
cube mean by that of the interval indicator, at the cube-power level. -/
theorem integerIntervalPeriodicCubeMean_eq_zeroExtension_ratio {q M d L : ℕ}
    [NeZero M] (hL : 0 < L) (hM : 2 * (L - 1) < M) (v : ZMod q → ℝ) :
    integerIntervalPeriodicCubeMean q d L v =
      subgroupCubeAverage (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L v) /
      subgroupCubeAverage (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L (fun _ => 1)) := by
  rw [intervalPeriodicZeroExtension_cube_average hL hM,
    intervalPeriodicZeroExtension_cube_average hL hM]
  simp only [integerPeriodicCubeProduct, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hc : (Fintype.card (ZMod M × (Fin d → ZMod M)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_div_div_cancel_right₀ hc]
  rfl

/-- The indicator denominator in the exact normalisation is strictly
positive, witnessed by the zero-increment interval cubes. -/
theorem intervalPeriodicZeroExtension_indicator_cube_pos {q M d L : ℕ}
    [NeZero M] (hL : 0 < L) (hM : 2 * (L - 1) < M) :
    0 < subgroupCubeAverage (⊤ : AddSubgroup (ZMod M)) d
      (intervalPeriodicZeroExtension q M L (fun _ => 1)) := by
  rw [intervalPeriodicZeroExtension_cube_average hL hM]
  simp only [integerPeriodicCubeProduct, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  apply div_pos
  · exact_mod_cast (integerIntervalCubeDomain_nonempty d L hL).card_pos
  · exact_mod_cast Fintype.card_pos

/-- Positivity for every periodic input on every nonempty interval follows
from finite cyclic cube positivity and the exact normalisation. No long-
period approximation or large-Gowers-norm hypothesis is needed. -/
theorem integerIntervalPeriodicCubeMean_nonneg_of_pos {q d L : ℕ}
    (hd : 0 < d) (hL : 0 < L) (v : ZMod q → ℝ) :
    0 ≤ integerIntervalPeriodicCubeMean q d L v := by
  let M := 2 * L + 1
  have hMp : 0 < M := by dsimp [M]; omega
  letI : NeZero M := ⟨Nat.ne_of_gt hMp⟩
  have hM : 2 * (L - 1) < M := by dsimp [M]; omega
  rw [integerIntervalPeriodicCubeMean_eq_zeroExtension_ratio (M := M) hL hM v]
  exact div_nonneg
    (subgroupCubeAverage_nonneg (⊤ : AddSubgroup (ZMod M)) d hd _)
    (intervalPeriodicZeroExtension_indicator_cube_pos (q := q) (d := d) hL hM).le

end Hindman168
