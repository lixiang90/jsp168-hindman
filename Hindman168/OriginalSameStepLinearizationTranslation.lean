import Hindman168.OriginalSameStepLinearizationAlgebra
import Hindman168.OriginalSameStepLinearizationSymbol

/-!
# Translation and right differences in the first shifted ideal

These are the polynomial membership statements needed by the exact integer
orbit construction.  In particular, the polynomial itself need not belong
to the first shifted ideal: its multiplicative right difference does.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 OAI.Erdos3.VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

section GeneralTranslation

variable {σ : Type*} [Fintype σ]

theorem translate_sub_mem_next (h : σ → ℚ) {k : ℕ}
    {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    translate h p - p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 1) := by
  intro α
  rw [coefficients_translate_sub]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1) -
      MvPolynomial.monomial β 1).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ (hp β)
    have hlt := (polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) β).2
      (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α <
      Finsupp.weight (fun _ : σ => 1) β at hlt
    omega

theorem translate_mem (h : σ → ℚ) {k : ℕ}
    {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    translate h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k := by
  have hd := F.shiftedAdaptedSubmodule_antitone (fun _ => 1) (Nat.le_succ k)
    (translate_sub_mem_next F h hp)
  simpa only [sub_add_cancel] using
    (F.shiftedAdaptedSubmodule (fun _ => 1) k).add_mem hd hp

end GeneralTranslation

section TranslationAlgebra

variable {σ : Type*}

noncomputable def translationLie (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ L :=
  substituteLie (fun i => MvPolynomial.X i + MvPolynomial.C (h i))

@[simp] theorem translationLie_apply (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    translationLie h p = translate h p := rfl

theorem translate_comp (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    translate h (translate k p) = translate (h + k) p := by
  change substitute (fun i => MvPolynomial.X i + MvPolynomial.C (h i))
    (substitute (fun i => MvPolynomial.X i + MvPolynomial.C (k i)) p) = _
  rw [substitute_comp]
  change substitute _ p = substitute (fun i => MvPolynomial.X i + MvPolynomial.C ((h + k) i)) p
  apply congrArg (fun f : σ → MvPolynomial σ ℚ => substitute f p)
  funext i
  simp only [map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Pi.add_apply, map_add]
  rw [add_assoc]

theorem translate_zero (p : VectorPolynomial σ ℚ L) :
    translate (0 : σ → ℚ) p = p := by
  change substitute (fun i => MvPolynomial.X i + MvPolynomial.C ((0 : σ → ℚ) i)) p = p
  simpa only [Pi.zero_apply, map_zero, add_zero] using substitute_X p

noncomputable def adaptedTranslation (h : σ → ℚ) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆
      F.adaptedLieSubalgebra (fun _ : σ => 1) where
  toFun p := ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
    (F.adapted_translate (fun _ => 1) (by simp) h
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩
  map_add' p q := Subtype.ext (map_add (translate h) p.val q.val)
  map_smul' c p := Subtype.ext (map_smul (translate h) c p.val)
  map_lie' {p q} := Subtype.ext ((translationLie h).map_lie p.val q.val)

@[simp] theorem adaptedTranslation_val (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (adaptedTranslation F h p).val = translate h p.val := rfl

theorem adaptedTranslation_comp (h k : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    adaptedTranslation F h (adaptedTranslation F k p) = adaptedTranslation F (h + k) p :=
  Subtype.ext (translate_comp h k p.val)

theorem adaptedTranslation_zero (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    adaptedTranslation F (0 : σ → ℚ) p = p := Subtype.ext (translate_zero p.val)

theorem adaptedTranslation_symbol (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    Symbols.polynomialSymbolMap F (fun _ => 1) (adaptedTranslation F h p) =
      Symbols.polynomialSymbolMap F (fun _ => 1) p :=
  Symbols.polynomialSymbolMap_translate F (fun _ => 1) (by simp) h p

/-- Logarithm of the multiplicative right difference belongs to `P₁`. -/
theorem rightDifference_mem (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    lieBCH s (-p) (adaptedTranslation F h p) ∈
      F.shiftedPolynomialIdeal (fun _ => 1) 1 := by
  apply (Symbols.polynomialSymbolMap_eq_zero_iff F (fun _ => 1) _).mp
  rw [map_lieBCH, map_neg, adaptedTranslation_symbol]
  exact lieBCH_neg_left (Symbols.polynomialSymbol_lowerCentralSeries_eq_bot F (fun _ => 1)) _

end TranslationAlgebra

noncomputable def fiberTranslation (d : ℕ) (h : Fin d → ℚ) :
    Fiber F d →ₗ⁅ℚ⁆ Fiber F d where
  toFun p := ⟨adaptedTranslation F h p.val, translate_mem F h p.property⟩
  map_add' p q := Subtype.ext (map_add (adaptedTranslation F h) p.val q.val)
  map_smul' c p := Subtype.ext (map_smul (adaptedTranslation F h) c p.val)
  map_lie' {p q} := Subtype.ext ((adaptedTranslation F h).map_lie p.val q.val)

@[simp] theorem fiberTranslation_val (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d) :
    (fiberTranslation F d h p).val = adaptedTranslation F h p.val := rfl

noncomputable def fiberTranslationEquiv (d : ℕ) (h : Fin d → ℚ) :
    Fiber F d ≃ₗ⁅ℚ⁆ Fiber F d where
  __ := fiberTranslation F d h
  invFun := fiberTranslation F d (-h)
  left_inv p := by
    apply Subtype.ext
    change adaptedTranslation F (-h) (adaptedTranslation F h p.val) = p.val
    rw [adaptedTranslation_comp, neg_add_cancel, adaptedTranslation_zero]
  right_inv p := by
    apply Subtype.ext
    change adaptedTranslation F h (adaptedTranslation F (-h) p.val) = p.val
    rw [adaptedTranslation_comp, add_neg_cancel, adaptedTranslation_zero]

/-- A same-step filtration on the polynomial fibre itself. -/
noncomputable def fiberFiltration (d : ℕ) : NilpotentLieFiltration (Fiber F d) s :=
  (F.adaptedPolynomialFiltration (fun _ : Fin d => 1)).restrictLieSubalgebra
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).toLieSubalgebra

abbrev FiberGroup (d : ℕ) := (fiberFiltration F d).Group

/-- A polynomial right difference as an actual element of the fibre BCH group. -/
noncomputable def differenceElement (d : ℕ) (h : Fin d → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) : FiberGroup F d :=
  ⟨⟨lieBCH s (-p) (adaptedTranslation F h p), rightDifference_mem F h p⟩⟩

noncomputable def fiberEvaluationLie (d : ℕ) (x : Fin d → ℚ) : Fiber F d →ₗ⁅ℚ⁆ L :=
  (evalLie x).comp ((F.adaptedLieSubalgebra (fun _ => 1)).incl.comp
    (F.shiftedPolynomialIdeal (fun _ => 1) 1).incl)

noncomputable def fiberEvaluation (d : ℕ) (x : Fin d → ℚ) : FiberGroup F d →* F.Group :=
  NilpotentLieBCHGroup.map (fiberEvaluationLie F d x)

@[simp] theorem fiberEvaluation_coord (d : ℕ) (x : Fin d → ℚ) (p : FiberGroup F d) :
    (fiberEvaluation F d x p).coord = eval x p.coord.val.val := rfl

/-- The right difference is the desired group difference at every rational input. -/
theorem differenceElement_evaluation (d : ℕ) (h x : Fin d → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    fiberEvaluation F d x (differenceElement F d h p) =
      (⟨eval x p.val⟩ : F.Group)⁻¹ * ⟨eval (x + h) p.val⟩ := by
  apply NilpotentLieBCHGroup.ext
  change eval x ((F.adaptedLieSubalgebra (fun _ : Fin d => 1)).incl
    (lieBCH s (-p) (adaptedTranslation F h p))) = _
  rw [map_lieBCH, map_neg, eval_lieBCH, map_neg]
  change lieBCH s (-eval x p.val) (eval x (translate h p.val)) =
    lieBCH s (-eval x p.val) (eval (x + h) p.val)
  exact congrArg (lieBCH s (-eval x p.val)) (eval_translate h x p.val)

end Hindman168.OriginalSameStepLinearization
