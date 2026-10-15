import Hindman168.OriginalSameStepLinearizationBasis

/-!
# A shift extension which preserves the original step

We use the first shifted polynomial ideal, whose coefficient of degree `j`
lies in filtration level `j + 1`.  The full adapted polynomial space would
only give the previously available doubled-step shift extension.  On this
smaller space differentiation raises the filtration by one, so adjoining
translation directions preserves the original step.

The polynomial and BCH definitions imported here are from OpenAI's fixed
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` source.  This file adds the restricted
action and its same-step filtration; it does not modify the imported source.
-/

namespace Hindman168

open OAI.Erdos3
open OAI.Erdos3.VectorPolynomial
open Module

namespace OriginalSameStepLinearization

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

/-- The polynomial fibre has coefficients in levels `degree + 1`. -/
noncomputable abbrev Fiber (d : ℕ) := F.shiftedPolynomialIdeal (fun _ : Fin d => 1) 1

noncomputable def derivative (d : ℕ) (h : Fin d → ℚ) :
    LieDerivation ℚ (Fiber F d) (Fiber F d) where
  toLinearMap :=
    { toFun := fun p => ⟨Calculus.adaptedDirectionalDerivative F h p.val,
        F.shiftedPolynomialIdeal_antitone (fun _ => 1) (by omega : 1 ≤ 1 + 1)
          (Calculus.adaptedDirectionalDerivative_mem_shifted F h 1 p.property)⟩
      map_add' := fun p q => Subtype.ext (map_add _ _ _)
      map_smul' := fun c p => Subtype.ext (map_smul _ _ _) }
  leibniz' p q := by
    apply Subtype.ext
    change Calculus.adaptedDirectionalDerivative F h ⁅p.val, q.val⁆ =
      ⁅p.val, Calculus.adaptedDirectionalDerivative F h q.val⁆ -
        ⁅q.val, Calculus.adaptedDirectionalDerivative F h p.val⁆
    rw [Calculus.adaptedDirectionalDerivative_lie F, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem derivative_val (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d) :
    (derivative F d h p).val = Calculus.adaptedDirectionalDerivative F h p.val := rfl

@[simp] theorem derivative_polynomial (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d) :
    ((derivative F d h p).val : VectorPolynomial (Fin d) ℚ L) =
      directionalDerivative h (p.val : VectorPolynomial (Fin d) ℚ L) := rfl

noncomputable def action (d : ℕ) :
    TimeTorus.Algebra d →ₗ⁅ℚ⁆ LieDerivation ℚ (Fiber F d) (Fiber F d) where
  toLinearMap :=
    { toFun := derivative F d
      map_add' := by
        intro h k
        apply LieDerivation.ext
        intro p
        apply Subtype.ext
        apply Subtype.ext
        exact directionalDerivative_direction_add h k p.val.val
      map_smul' := by
        intro c h
        apply LieDerivation.ext
        intro p
        apply Subtype.ext
        apply Subtype.ext
        exact directionalDerivative_direction_smul c h p.val.val }
  map_lie' {h k} := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    apply Subtype.ext
    rw [TimeTorus.lie_eq_zero]
    change directionalDerivative (0 : Fin d → ℚ) p.val.val =
      directionalDerivative h (directionalDerivative k p.val.val) -
        directionalDerivative k (directionalDerivative h p.val.val)
    rw [Calculus.directionalDerivative_commute]
    simp only [sub_self, directionalDerivative, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, LinearMap.zero_apply]

/-- The actual rational Lie algebra `P₁ ⋊ ℚᵈ`. -/
abbrev Algebra (d : ℕ) :=
  LieAlgebra.SemiDirectSum (Fiber F d) (TimeTorus.Algebra d) (action F d)

noncomputable def layer (d k : ℕ) : Submodule ℚ (Algebra F d) where
  carrier := {x | x.left.val ∈ F.shiftedPolynomialIdeal (fun _ => 1) k ∧
    x.right ∈ (TimeTorus.filtration d).layer k}
  zero_mem' := ⟨(F.shiftedPolynomialIdeal (fun _ => 1) k).zero_mem, Submodule.zero_mem _⟩
  add_mem' hx hy := ⟨(F.shiftedPolynomialIdeal (fun _ => 1) k).add_mem hx.1 hy.1,
    Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' c _ hx := ⟨(F.shiftedPolynomialIdeal (fun _ => 1) k).smul_mem c hx.1,
    Submodule.smul_mem _ c hx.2⟩

theorem layer_antitone (d : ℕ) : Antitone (layer F d) := by
  intro i j hij x hx
  exact ⟨F.shiftedPolynomialIdeal_antitone (fun _ => 1) hij hx.1,
    (TimeTorus.filtration d).antitone hij hx.2⟩

theorem layer_one (d : ℕ) : layer F d 1 = ⊤ := by
  apply top_unique
  intro x _
  exact ⟨x.left.property, by rw [(TimeTorus.filtration d).one_eq_top]; trivial⟩

theorem derivative_mem (d : ℕ) {i j : ℕ}
    {h : TimeTorus.Algebra d} {p : Fiber F d}
    (hh : h ∈ (TimeTorus.filtration d).layer i)
    (hp : p.val ∈ F.shiftedPolynomialIdeal (fun _ => 1) j) :
    (derivative F d h p).val ∈ F.shiftedPolynomialIdeal (fun _ => 1) (i + j) := by
  by_cases hi : i ≤ 1
  · exact F.shiftedPolynomialIdeal_antitone (fun _ => 1) (by omega)
      (Calculus.adaptedDirectionalDerivative_mem_shifted F h j hp)
  · have hz : h = 0 := by
      simpa only [TimeTorus.filtration, hi, ite_false, Submodule.mem_bot] using hh
    rw [hz]
    change directionalDerivative (0 : Fin d → ℚ) p.val.val ∈
      F.shiftedAdaptedSubmodule (fun _ => 1) (i + j)
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      LinearMap.zero_apply, Submodule.zero_mem]

theorem layer_lie (d : ℕ) {i j : ℕ} {x y : Algebra F d}
    (hx : x ∈ layer F d i) (hy : y ∈ layer F d j) :
    ⁅x, y⁆ ∈ layer F d (i + j) := by
  constructor
  · change ⁅x.left.val, y.left.val⁆ + (derivative F d x.right y.left).val -
      (derivative F d y.right x.left).val ∈ F.shiftedPolynomialIdeal (fun _ => 1) (i + j)
    apply (F.shiftedPolynomialIdeal (fun _ => 1) (i + j)).sub_mem
    · exact (F.shiftedPolynomialIdeal (fun _ => 1) (i + j)).add_mem
        (F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) hx.1 hy.1)
        (derivative_mem F d hx.2 hy.1)
    · rw [Nat.add_comm i j]
      exact derivative_mem F d hy.2 hx.1
  · exact Submodule.zero_mem _

theorem layer_terminal (hs : 1 ≤ s) (d : ℕ) : layer F d (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    apply Subtype.ext
    change x.left.val.val = 0
    apply coefficients.injective
    ext α
    have h := F.antitone (Nat.le_add_left (s + 1) _ ) (hx.1 α)
    change coefficients x.left.val.val α ∈ F.layer (s + 1) at h
    rw [F.terminal, Submodule.mem_bot] at h
    simpa only [map_zero, Finsupp.zero_apply] using h
  · change x.right = 0
    have hi : ¬s + 1 ≤ 1 := by omega
    simpa only [TimeTorus.filtration, hi, ite_false, Submodule.mem_bot] using hx.2

/-- The step is `s`, without replacing it by a larger integer. -/
noncomputable def filtration (hs : 1 ≤ s) (d : ℕ) :
    NilpotentLieFiltration (Algebra F d) s where
  layer := layer F d
  antitone := layer_antitone F d
  one_eq_top := layer_one F d
  lie_mem := layer_lie F d
  terminal := layer_terminal F hs d

theorem lowerCentralSeries_eq_bot (hs : 1 ≤ s) (d : ℕ) :
    LieModule.lowerCentralSeries ℚ (Algebra F d) (Algebra F d) s = ⊥ :=
  (filtration F hs d).lowerCentralSeries_eq_bot

abbrev Group (hs : 1 ≤ s) (d : ℕ) := (filtration F hs d).Group

theorem nilpotencyClass_le (hs : 1 ≤ s) (d : ℕ) :
    _root_.Group.nilpotencyClass (Group F hs d) ≤ s :=
  (filtration F hs d).nilpotencyClass_le

section Basis

variable {ι : Type*} (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def basis (d : ℕ) :
    Basis (BasisTools.ShiftedMonomialIndex (fun _ : Fin d => 1) ω 1 ⊕ Fin d)
      ℚ (Algebra F d) :=
  ((BasisTools.shiftedMonomialBasis F b ω hF (fun _ : Fin d => 1) 1).prod (TimeTorus.basis d)).map
    (LieAlgebra.SemiDirectSum.toProdl (action F d)).symm

include b hF in
theorem finiteDimensional [Fintype ι] (hω : ∀ i, ω i ≤ s) (d : ℕ) :
    FiniteDimensional ℚ (Algebra F d) := by
  let w : Fin d → ℕ := fun _ => 1
  letI : Finite (BasisTools.AdaptedBasisIndex w ω) :=
    BasisTools.adaptedBasisIndex_finite w ω s (by simp [w]) hω
  exact (basis F b ω hF d).finiteDimensional_of_finite

end Basis

/-- Finite-dimensionality needs no bounds or assumptions on orbit coefficients. -/
theorem finiteDimensional_of_finite [FiniteDimensional ℚ L] (d : ℕ) :
    FiniteDimensional ℚ (Algebra F d) := by
  obtain ⟨b, ω, _, _, hF⟩ := F.exists_sorted_adapted_basis
  have hω (i) : ω i ≤ s := by
    by_contra hi
    have hbi : b i ∈ F.layer (s + 1) := by
      rw [hF]
      exact Submodule.subset_span ⟨i, Nat.succ_le_of_lt (Nat.lt_of_not_ge hi), rfl⟩
    rw [F.terminal, Submodule.mem_bot] at hbi
    exact b.ne_zero i hbi
  exact finiteDimensional F b ω hF hω d

/-- The first shifted ideal has finite dimension as well. -/
theorem fiber_finiteDimensional [FiniteDimensional ℚ L] (d : ℕ) :
    FiniteDimensional ℚ (Fiber F d) := by
  letI := finiteDimensional_of_finite F d
  exact FiniteDimensional.of_injective
    (LieAlgebra.SemiDirectSum.inl (action F d)).toLinearMap
    (LieAlgebra.SemiDirectSum.inl_injective (action F d))

end OriginalSameStepLinearization
end Hindman168
