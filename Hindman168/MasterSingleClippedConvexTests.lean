import Hindman168.MasterUniformClippedDualProducts
import Hindman168.FinitePolynomialHullBound

/-!
# Actual signed single-template tests and their closed convex hull

The finite mass, conditioned local prime law and quotient shifts are the
original ones. Every product estimate is derived from the actual uniform
mixed-dual theorem; no desired polynomial correlation premise is supplied.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

structure OriginalSingleDualInput (a d : ℕ) where
  epsilon : (Fin a → ℕ) → ℝ
  vertexTest : (Fin a → ℕ) → CubeVertex d → ℤ → ℝ

def OriginalSingleDualInput.Admissible {a d m : ℕ} (u : OriginalSingleDualInput a d)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m) (w : ℕ) : Prop :=
  (∀ x, |u.epsilon x| ≤ 1) ∧
    (∀ x S y, |u.vertexTest x S y| ≤ 1 + masterPredictionBlockMask F C label w y)

noncomputable def signedOriginalSingleClippedClass {a d N K m : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (cut : ℝ) (w : ℕ) : Set (ℤ → ℝ) :=
  {f | ∃ (sign : ℝ) (u : OriginalSingleDualInput a d), |sign| = 1 ∧
    u.Admissible F C label w ∧ f = fun y => sign * predictionClip cut
      (masterSingleGoodDualTest F d gap J choice tests den
        (fun _ => u.epsilon) (fun _ => u.vertexTest) w y)}

theorem MasterParameterConditions.uniform_single_signed_clipped_products
    {n a N m d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0) (hd : 0 < d)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut)
    (b : ℕ) : ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ f : Fin b → ℤ → ℝ,
        (∀ q, f q ∈ signedOriginalSingleClippedClass (a := a) (d := d)
          F C label gap J choice tests den cut w) →
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q, f q y)| < η := by
  let e := Fintype.equivFin (Σ _q : Fin b, Fin a)
  have htg (_p : Fin 1) : ∀ᶠ w in atTop,
      ∀ _q : Fin b, tail w ⊆ Finset.range (gap w).val := htailgap.mono (fun _ hw _ => hw)
  have hgg (_p : Fin 1) : ∀ᶠ w in atTop,
      ∀ _q : Fin b, (gap w).val ≤ (root w).val := hgap.mono (fun _ hw _ => hw)
  have hu := hF.uniform_clipped_dual_products hD
    (fun (_p : Fin 1) (_q : Fin b) => d) (fun _ _ => a)
    (fun _ _ => le_rfl) (fun _ _ => hd) (fun _ => Fintype.card (Σ _q : Fin b, Fin a))
    (fun _ => e) C hN label tail htail root (fun _ w _ => gap w) htailroot htg hgg
    J hJ (fun _ w _ => choice w) (fun _ _ => tests) (fun _ _ => den)
    (fun _ _ => hden) (fun _ _ => masterSlot) (fun _ _ => hmasterSlot)
    (fun _ _ => hinclude) cut hcut
  intro η hη
  filter_upwards [hu η hη] with w hw
  intro f hf
  choose sign input hsign hinput heq using hf
  let u : OriginalDualInputFamily (fun (_p : Fin 1) (_q : Fin b) => d)
      (fun _ _ => a) :=
    ⟨fun _ q => (input q).epsilon, fun _ q => (input q).vertexTest⟩
  have hadm : u.Admissible F C label w :=
    ⟨fun _ q => (hinput q).1, fun _ q => (hinput q).2⟩
  have hh := hw 0 u hadm
  let clipped q y := predictionClip cut
    (masterReplicaGoodDualTest F (fun _ : Fin b => d) (fun _ => a)
      (fun w _ => gap w) J (fun w _ => choice w) (fun _ => tests) (fun _ => den)
      (fun _ => u.epsilon 0) (fun _ => u.vertexTest 0) w q y)
  have hpoint (q : Fin b) (y : ℤ) : f q y = sign q * clipped q y := by
    exact congrFun (heq q) y
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

theorem MasterParameterConditions.uniform_single_clipped_hull_polynomial
    {n a N m d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0) (hd : 0 < d)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) (P : Polynomial ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ G ∈ closedConvexHull ℝ (signedOriginalSingleClippedClass (a := a) (d := d)
        F C label gap J choice tests den cut w),
      |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (masterPredictionBlockMask F C label w y - 1) * P.eval (G y))| < η := by
  apply uniform_polynomial_closedConvexHull
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => masterPredictionBlockMask F C label w y - 1)
    (fun w => signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w)
    ?_ P
  intro b η hη
  exact (hF.uniform_single_signed_clipped_products hD hd C hN label tail htail root gap
    htailroot htailgap hgap J hJ choice tests den hden masterSlot hmasterSlot hinclude cut hcut
    b η hη).mono (fun _ hw f hf => (hw f hf).le)

end Hindman168
