import Hindman168.OriginalSameStepLinearizationTranslation
import Hindman168.OriginalSameStepLinearizationRealization

/-!
# Real coefficients in the same-step construction

The finite-dimensional model is the scalar extension of a rational Lie
algebra.  Arbitrary real polynomial coefficients are lifted to that scalar
extension, rather than being put into the rational lattice.  The right
multiplicative difference lies in the scalar extension of the first shifted
ideal, by the exact kernel identity for scalar extension.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 OAI.Erdos3.VectorPolynomial Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

abbrev RealFiberGroup (d : ℕ) := (fiberFiltration F d).realification.Group

noncomputable def realAdaptedTranslation {σ : Type*} (h : σ → ℚ) :
    RealAdaptedGroup F (fun _ : σ => 1) →*
      RealAdaptedGroup F (fun _ : σ => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    (adaptedTranslation F h)

noncomputable def realFiberInclusion (d : ℕ) :
    RealFiberGroup F d →* RealAdaptedGroup F (fun _ : Fin d => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (fiberFiltration F d).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration (fun _ : Fin d => 1)).lowerCentralSeries_eq_bot)
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).incl

noncomputable def realFiberTranslation (d : ℕ) (h : Fin d → ℚ) :
    RealFiberGroup F d →* RealFiberGroup F d :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (fiberFiltration F d).lowerCentralSeries_eq_bot)
    (hM := (fiberFiltration F d).lowerCentralSeries_eq_bot) (fiberTranslation F d h)

noncomputable def adaptedEvaluationLie {σ : Type*} (x : σ → ℚ) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆ L :=
  (evalLie x).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl

noncomputable def realAdaptedEvaluation {σ : Type*} (x : σ → ℚ) :
    RealAdaptedGroup F (fun _ : σ => 1) →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) (adaptedEvaluationLie F x)

noncomputable def realFiberEvaluation (d : ℕ) (x : Fin d → ℚ) :
    RealFiberGroup F d →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (fiberFiltration F d).lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) (fiberEvaluationLie F d x)

section Symbol

variable {σ : Type*}

/-- Translation fixes the polynomial symbol also for arbitrary real
    coefficients. -/
theorem realTranslation_symbol (h : σ → ℚ)
    (p : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    realificationLieHom (Symbols.polynomialSymbolMap F (fun _ => 1))
        (realificationLieHom (adaptedTranslation F h) p) =
      realificationLieHom (Symbols.polynomialSymbolMap F (fun _ => 1)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => simp only [realificationLieHom_tmul, adaptedTranslation_symbol]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The difference belongs to the real span of the rational first shifted
    ideal.  In particular this statement does not require rational orbit
    coefficients. -/
theorem real_rightDifference_mem (h : σ → ℚ)
    (p : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    lieBCH s (-p) (realificationLieHom (adaptedTranslation F h) p) ∈
      (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule.baseChange ℝ := by
  apply (realification_mkQ_eq_zero_iff
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule _).mp
  change realLieHomToRat (realificationLieHom (Symbols.polynomialSymbolMap F (fun _ => 1)))
    (lieBCH s (-p) (realificationLieHom (adaptedTranslation F h) p)) = 0
  rw [map_lieBCH, map_neg]
  change lieBCH s
    (-realificationLieHom (Symbols.polynomialSymbolMap F (fun _ => 1)) p)
    (realificationLieHom (Symbols.polynomialSymbolMap F (fun _ => 1))
      (realificationLieHom (adaptedTranslation F h) p)) = 0
  rw [realTranslation_symbol]
  exact lieBCH_neg_left
    (realification_lowerCentralSeries_eq_bot
      (Symbols.polynomialSymbol_lowerCentralSeries_eq_bot F (fun _ => 1))) _

end Symbol

noncomputable def realDifferenceElement (d : ℕ) (h : Fin d → ℚ)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) : RealFiberGroup F d :=
  ⟨(realificationSubmoduleEquiv
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule).symm
      ⟨lieBCH s (-p.coord) (realificationLieHom (adaptedTranslation F h) p.coord),
        real_rightDifference_mem F h p.coord⟩⟩

/-- The lifted fibre element is exactly the right multiplicative difference. -/
theorem realDifferenceElement_inclusion (d : ℕ) (h : Fin d → ℚ)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    realFiberInclusion F d (realDifferenceElement F d h p) =
      p⁻¹ * realAdaptedTranslation F h p := by
  apply NilpotentLieBCHGroup.ext
  exact congrArg Subtype.val ((realificationSubmoduleEquiv
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule).apply_symm_apply _)

/-- Evaluation of scalar-extended adapted polynomials agrees with evaluation
    of their real-coefficient polynomial realization. -/
theorem realAdaptedEvaluation_coord {σ : Type*} (x : σ → ℚ)
    (p : RealAdaptedGroup F (fun _ : σ => 1)) :
    (realAdaptedEvaluation F x p).coord =
      eval x (Realization.realAdaptedPolynomialMap F (fun _ => 1) p.coord) := by
  change realificationLieHom (adaptedEvaluationLie F x) p.coord = _
  induction p.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    change a ⊗ₜ[ℚ] eval x p.val =
      eval x (Realization.realificationLieEquiv (a ⊗ₜ[ℚ] p.val))
    exact (Realization.eval_realificationLieEquiv_tmul a p.val x).symm
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Fibre evaluation factors through the full adapted polynomial group. -/
theorem realFiberEvaluation_inclusion (d : ℕ) (x : Fin d → ℚ)
    (p : RealFiberGroup F d) :
    realAdaptedEvaluation F x (realFiberInclusion F d p) =
      realFiberEvaluation F d x p := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (adaptedEvaluationLie F x)
    (realificationLieHom (F.shiftedPolynomialIdeal (fun _ => 1) 1).incl p.coord) =
      realificationLieHom (fiberEvaluationLie F d x) p.coord
  induction p.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rfl
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Evaluation and rational translation commute before and after scalar
    extension. -/
theorem realAdaptedEvaluation_translation {σ : Type*} (x h : σ → ℚ)
    (p : RealAdaptedGroup F (fun _ : σ => 1)) :
    realAdaptedEvaluation F x (realAdaptedTranslation F h p) =
      realAdaptedEvaluation F (x + h) p := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (adaptedEvaluationLie F x)
    (realificationLieHom (adaptedTranslation F h) p.coord) =
      realificationLieHom (adaptedEvaluationLie F (x + h)) p.coord
  induction p.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [realificationLieHom_tmul]
    congr 1
    exact eval_translate h x p.val
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Exact evaluation of the real right difference, at every rational time. -/
theorem realDifferenceElement_evaluation (d : ℕ) (h x : Fin d → ℚ)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    realFiberEvaluation F d x (realDifferenceElement F d h p) =
      (realAdaptedEvaluation F x p)⁻¹ * realAdaptedEvaluation F (x + h) p := by
  rw [← realFiberEvaluation_inclusion, realDifferenceElement_inclusion,
    map_mul, map_inv, realAdaptedEvaluation_translation]


/-- Constants belong to the first shifted ideal, including nonzero initial
    values. Their inclusion will serve as the orbit basepoint. -/
noncomputable def fiberConstantLie (d : ℕ) : L →ₗ⁅ℚ⁆ Fiber F d where
  toFun x := ⟨F.adaptedConstant (fun _ => 1) x,
    F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) x⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change monomial 0 (x + y) = monomial 0 x + monomial 0 y
    simp only [monomial, TensorProduct.tmul_add]
  map_smul' c x := by
    apply Subtype.ext
    apply Subtype.ext
    change monomial 0 (c • x) = c • monomial 0 x
    simp only [monomial, TensorProduct.tmul_smul]
  map_lie' {x y} := by
    apply Subtype.ext
    apply Subtype.ext
    change monomial 0 ⁅x, y⁆ = ⁅monomial 0 x, monomial 0 y⁆
    rw [lie_monomial, zero_add]

noncomputable def realFiberConstant (d : ℕ) : F.realification.Group →* RealFiberGroup F d :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.lowerCentralSeries_eq_bot)
    (hM := (fiberFiltration F d).lowerCentralSeries_eq_bot) (fiberConstantLie F d)

@[simp] theorem realFiberEvaluation_constant (d : ℕ) (x : Fin d → ℚ)
    (g : F.realification.Group) :
    realFiberEvaluation F d x (realFiberConstant F d g) = g := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (fiberEvaluationLie F d x)
    (realificationLieHom (fiberConstantLie F d) g.coord) = g.coord
  induction g.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul a g =>
    simp only [realificationLieHom_tmul]
    change a ⊗ₜ[ℚ] eval x (monomial 0 g) = a ⊗ₜ[ℚ] g
    simp only [eval_monomial, Finsupp.prod_zero_index, one_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- A rational rescaling of the variable preserves adaptedness. -/
noncomputable def adaptedDilation {σ : Type*} (r : ℚ) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆
      F.adaptedLieSubalgebra (fun _ : σ => 1) where
  toFun p := ⟨weightedDilation (fun _ => 1) r p.val, by
    intro α
    rw [coefficients_weightedDilation]
    exact (F.layer _).smul_mem _ (p.property α)⟩
  map_add' p q := Subtype.ext (map_add (weightedDilation (fun _ => 1) r) p.val q.val)
  map_smul' c p := Subtype.ext (map_smul (weightedDilation (fun _ => 1) r) c p.val)
  map_lie' {p q} := Subtype.ext (weightedDilation_lie (fun _ => 1) r p.val q.val)

noncomputable def realAdaptedDilation {σ : Type*} (r : ℚ) :
    RealAdaptedGroup F (fun _ : σ => 1) →*
      RealAdaptedGroup F (fun _ : σ => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    (adaptedDilation F r)

/-- The clock can be enlarged to an integer lattice period without changing
    the original sampled sequence. -/
theorem realAdaptedEvaluation_dilation {σ : Type*} (r : ℚ) (x : σ → ℚ)
    (p : RealAdaptedGroup F (fun _ : σ => 1)) :
    realAdaptedEvaluation F x (realAdaptedDilation F r p) =
      realAdaptedEvaluation F (r • x) p := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (adaptedEvaluationLie F x)
    (realificationLieHom (adaptedDilation F r) p.coord) =
      realificationLieHom (adaptedEvaluationLie F (r • x)) p.coord
  induction p.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [realificationLieHom_tmul]
    congr 1
    change eval x (weightedDilation (fun _ => 1) r p.val) = eval (r • x) p.val
    have he := eval_weightedDilation (fun _ => 1) r x p.val
    change eval x (weightedDilation (fun _ => 1) r p.val) =
      eval (fun i => r ^ 1 * x i) p.val at he
    simp only [pow_one] at he
    change eval x (weightedDilation (fun _ => 1) r p.val) =
      eval (fun i => r * x i) p.val
    exact he
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Every real-coefficient polynomial orbit is represented in the scalar
    extension of the rational adapted polynomial Lie algebra. -/
theorem exists_realAdaptedEvaluation_lift [FiniteDimensional ℚ L] {σ : Type*}
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    ∃ q : RealAdaptedGroup F (fun _ : σ => 1),
      ∀ x : σ → ℤ, realAdaptedEvaluation F (fun i => (x i : ℚ)) q =
        F.realification.polynomialOrbitEval (fun _ => 1) x p := by
  obtain ⟨b, ω, _, _, hF⟩ := F.exists_sorted_adapted_basis
  let a : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨p.log, (F.realification.mem_adaptedSubmodule (fun _ => 1) p.log).mpr p.adapted⟩
  obtain ⟨q, hq⟩ := Realization.realAdaptedPolynomialTensor_surjective F (fun _ : σ => 1) b ω hF a
  refine ⟨⟨q⟩, fun x => ?_⟩
  apply NilpotentLieBCHGroup.ext
  rw [realAdaptedEvaluation_coord]
  change eval (fun i => (x i : ℚ)) (Realization.realAdaptedPolynomialTensor F (fun _ => 1) q).val =
    eval (fun i => (x i : ℚ)) a.val
  rw [hq]

end Hindman168.OriginalSameStepLinearization
