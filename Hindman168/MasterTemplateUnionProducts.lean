import Hindman168.OriginalDualTemplates

/-!
# Actual uniform signed products across heterogeneous local templates

Every tuple of template choices has its own dependent dimensions and prime
arities. There are finitely many tuples at each fixed replica count, so the
actual uniform product estimate holds across the whole union. No independent
prime law is merged when a template or gap is repeated.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.uniform_template_union_products
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut)
    (b : ℕ) : ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ f : Fin b → ℤ → ℝ, (∀ q, f q ∈ signedOriginalClippedUnion T F C label J cut w) →
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, f q y)| < η := by
  intro η hη
  have hprofile (φ : Fin b → Fin L) : ∀ᶠ w in atTop,
      ∀ f : Fin b → ℤ → ℝ,
        (∀ q, f q ∈ signedOriginalSingleClippedClass (a := (T (φ q)).arity)
          (d := (T (φ q)).dimension) F C label (T (φ q)).gap J (T (φ q)).choice
          (T (φ q)).tests (T (φ q)).denominator cut w) →
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, f q y)| < η := by
    let dim (q : Fin b) := (T (φ q)).dimension
    let arity (q : Fin b) := (T (φ q)).arity
    let e := Fintype.equivFin (Σ q : Fin b, Fin (arity q))
    have htg (_p : Fin 1) : ∀ᶠ w in atTop,
        ∀ q : Fin b, tail w ⊆ Finset.range ((T (φ q)).gap w).val :=
      eventually_all.mpr (fun q => (hT (φ q)).tail_gap)
    have hgg (_p : Fin 1) : ∀ᶠ w in atTop,
        ∀ q : Fin b, ((T (φ q)).gap w).val ≤ (root w).val :=
      eventually_all.mpr (fun q => (hT (φ q)).gap_root)
    have hu := hF.uniform_clipped_dual_products hD
      (fun (_p : Fin 1) q => dim q) (fun _ q => arity q)
      (fun _ q => (hT (φ q)).dimension_le) (fun _ q => (hT (φ q)).dimension_pos)
      (fun _ => Fintype.card (Σ q : Fin b, Fin (arity q))) (fun _ => e)
      C hN label tail htail root (fun _ w q => (T (φ q)).gap w) htailroot htg hgg
      J hJ (fun _ w q => (T (φ q)).choice w) (fun _ q => (T (φ q)).tests)
      (fun _ q => (T (φ q)).denominator) (fun _ q => (T (φ q)).denominator_mem)
      (fun _ q => (T (φ q)).masterSlot) (fun _ q => (T (φ q)).masterSlot_injective)
      (fun _ q => (hT (φ q)).polynomial_inclusion) cut hcut
    filter_upwards [hu η hη] with w hw
    intro f hf
    choose sign input hsign hinput heq using hf
    let u : OriginalDualInputFamily (fun (_p : Fin 1) q => dim q) (fun _ q => arity q) :=
      ⟨fun _ q => (input q).epsilon, fun _ q => (input q).vertexTest⟩
    have hadm : u.Admissible F C label w :=
      ⟨fun _ q => (hinput q).1, fun _ q => (hinput q).2⟩
    have hh := hw 0 u hadm
    let clipped q y := predictionClip cut
      (masterReplicaGoodDualTest F dim arity (fun w q => (T (φ q)).gap w) J
        (fun w q => (T (φ q)).choice w) (fun q => (T (φ q)).tests)
        (fun q => (T (φ q)).denominator) (fun _ => u.epsilon 0)
        (fun _ => u.vertexTest 0) w q y)
    have hpoint (q : Fin b) (y : ℤ) : f q y = sign q * clipped q y :=
      congrFun (heq q) y
    have he : expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, f q y) =
        (∏ q, sign q) * expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, clipped q y) := by
      simp_rw [hpoint, Finset.prod_mul_distrib]
      rw [← expectation_const_mul]
      apply congrArg (expectation _)
      funext y
      ring
    rw [he, abs_mul, Finset.abs_prod]
    simp only [hsign, Finset.prod_const_one, one_mul]
    exact hh
  have hall : ∀ᶠ w in atTop, ∀ φ : Fin b → Fin L,
      ∀ f : Fin b → ℤ → ℝ,
        (∀ q, f q ∈ signedOriginalSingleClippedClass (a := (T (φ q)).arity)
          (d := (T (φ q)).dimension) F C label (T (φ q)).gap J (T (φ q)).choice
          (T (φ q)).tests (T (φ q)).denominator cut w) →
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, f q y)| < η :=
    eventually_all.mpr hprofile
  filter_upwards [hall] with w hw
  intro f hf
  have hc (q : Fin b) := Set.mem_iUnion.mp (hf q)
  choose φ hφ using hc
  exact hw φ f hφ

theorem MasterParameterConditions.uniform_template_union_hull_polynomial
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) (P : Polynomial ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ G ∈ closedConvexHull ℝ (signedOriginalClippedUnion T F C label J cut w),
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * P.eval (G y))| < η := by
  apply uniform_polynomial_closedConvexHull
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => masterPredictionBlockMask F C label w y - 1)
    (fun w => signedOriginalClippedUnion T F C label J cut w) ?_ P
  intro b η hη
  exact (hF.uniform_template_union_products hD T C hN label tail htail root htailroot hT J hJ
    cut hcut b η hη).mono (fun _ hw f hf => (hw f hf).le)

end Hindman168
