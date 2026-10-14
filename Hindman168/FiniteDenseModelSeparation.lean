import Hindman168.FinitePositivePartHull
import Mathlib.Topology.Sion
import Mathlib.Topology.Order.Compact

/-!
# Bounded dense models from actual finite weighted pairings

Sion minimax is applied to compact coordinate cubes and the bounded closed
convex test hull in the product topology. Expectations have finite support;
no extra integration or minimax conclusion is supplied as a premise.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Topology Classical

noncomputable def modelPairing {α : Type*} (μ : Mass α) (ρ F G : α → ℝ) : ℝ :=
  expectation μ (fun x => (ρ x - F x) * G x)

theorem modelPairing_affine_left {α : Type*} (μ : Mass α) (ρ F₁ F₂ G : α → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    modelPairing μ ρ (a • F₁ + b • F₂) G =
      a * modelPairing μ ρ F₁ G + b * modelPairing μ ρ F₂ G := by
  unfold modelPairing
  rw [← expectation_const_mul, ← expectation_const_mul, ← expectation_add]
  apply congrArg (expectation μ)
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(ρ x * G x) * hab

theorem modelPairing_affine_right {α : Type*} (μ : Mass α) (ρ F G₁ G₂ : α → ℝ)
    (a b : ℝ) :
    modelPairing μ ρ F (a • G₁ + b • G₂) =
      a * modelPairing μ ρ F G₁ + b * modelPairing μ ρ F G₂ := by
  unfold modelPairing
  rw [← expectation_const_mul, ← expectation_const_mul, ← expectation_add]
  apply congrArg (expectation μ)
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def positivePartModel {α : Type*} (G : α → ℝ) : α → ℝ :=
  fun x => if 0 ≤ G x then 1 else 0

theorem positivePartModel_mem_cube {α : Type*} (G : α → ℝ) :
    positivePartModel G ∈ Set.Icc (0 : α → ℝ) 1 := by
  constructor <;> intro x <;> simp only [positivePartModel] <;> split_ifs <;> norm_num

theorem positivePartModel_pairing_le {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (ρ ν G : α → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x) :
    modelPairing μ ρ (positivePartModel G) G ≤
      expectation μ (fun x => (ν x - 1) * max (G x) 0) := by
  apply expectation_mono _ _ _ hμ
  intro x
  by_cases hx : 0 ≤ G x
  · simp only [positivePartModel, if_pos hx, max_eq_left hx]
    exact mul_le_mul_of_nonneg_right (by linarith [(hρ x).2]) hx
  · simp only [positivePartModel, if_neg hx, sub_zero, max_eq_right (le_of_not_ge hx), mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hρ x).1 (le_of_not_ge hx)

theorem isCompact_bounded_closedConvexHull {α : Type*} (S : Set (α → ℝ)) (K : ℝ)
    (hS : ∀ f ∈ S, ∀ x, |f x| ≤ K) : IsCompact (closedConvexHull ℝ S) := by
  apply (isCompact_Icc (a := fun _ : α => -K) (b := fun _ => K)).of_isClosed_subset
    isClosed_closedConvexHull
  intro G hG
  have hg := closedConvexHull_abs_le S K hS hG
  exact ⟨fun x => (abs_le.mp (hg x)).1, fun x => (abs_le.mp (hg x)).2⟩

theorem bounded_dense_model_of_positive_part {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (ρ ν : α → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x) (S : Set (α → ℝ))
    (hne : S.Nonempty) (K : ℝ) (hS : ∀ f ∈ S, ∀ x, |f x| ≤ K)
    (hneg : ∀ f ∈ S, -f ∈ S) (η : ℝ)
    (hpos : ∀ G ∈ closedConvexHull ℝ S,
      expectation μ (fun x => (ν x - 1) * max (G x) 0) ≤ η) :
    ∃ F : α → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧
      ∀ g ∈ S, |expectation μ (fun x => (ρ x - F x) * g x)| ≤ η := by
  let X : Set (α → ℝ) := Set.Icc 0 1
  let Y := closedConvexHull ℝ S
  have hX : Convex ℝ X := convex_Icc _ _
  have hY : Convex ℝ Y := convex_closedConvexHull
  have hneX : X.Nonempty := ⟨0, le_rfl, by intro x; norm_num⟩
  have hneY : Y.Nonempty := hne.mono subset_closedConvexHull
  have hcX : IsCompact X := isCompact_Icc
  have hcY : IsCompact Y := isCompact_bounded_closedConvexHull S K hS
  have hleft (G : α → ℝ) (_hG : G ∈ Y) :
      LowerSemicontinuousOn (fun F => modelPairing μ ρ F G) X := by
    have hc : Continuous (fun F => modelPairing μ ρ F G) := by
      unfold modelPairing expectation Finsupp.sum
      fun_prop
    exact hc.continuousOn.lowerSemicontinuousOn
  have hleftConv (G : α → ℝ) (_hG : G ∈ Y) :
      QuasiconvexOn ℝ X (fun F => modelPairing μ ρ F G) := by
    apply ConvexOn.quasiconvexOn
    refine ⟨hX, ?_⟩
    intro F₁ _ F₂ _ a b _ _ hab
    exact (modelPairing_affine_left μ ρ F₁ F₂ G a b hab).le
  have hright (F : α → ℝ) (_hF : F ∈ X) :
      UpperSemicontinuousOn (fun G => modelPairing μ ρ F G) Y := by
    have hc : Continuous (fun G => modelPairing μ ρ F G) := by
      unfold modelPairing expectation Finsupp.sum
      fun_prop
    exact hc.continuousOn.upperSemicontinuousOn
  have hrightConc (F : α → ℝ) (_hF : F ∈ X) :
      QuasiconcaveOn ℝ Y (fun G => modelPairing μ ρ F G) := by
    apply ConcaveOn.quasiconcaveOn
    refine ⟨hY, ?_⟩
    intro G₁ _ G₂ _ a b _ _ _
    exact (modelPairing_affine_right μ ρ F G₁ G₂ a b).ge
  obtain ⟨F, hF, G₀, hG₀, hsaddle⟩ := Sion.exists_isSaddlePointOn hneX hX hcX
    hleft hleftConv hY hneY hcY hright hrightConc
  have hupper (g : α → ℝ) (hg : g ∈ S) : modelPairing μ ρ F g ≤ η :=
    (hsaddle (positivePartModel G₀) (positivePartModel_mem_cube G₀) g
      (subset_closedConvexHull hg)).trans
        ((positivePartModel_pairing_le μ hμ ρ ν G₀ hρ).trans (hpos G₀ hG₀))
  refine ⟨F, fun x => ⟨hF.1 x, hF.2 x⟩, ?_⟩
  intro g hg
  apply abs_le.mpr
  constructor
  · change -η ≤ modelPairing μ ρ F g
    have hn := hupper (-g) (hneg g hg)
    have he : modelPairing μ ρ F (-g) = -modelPairing μ ρ F g := by
      unfold modelPairing expectation Finsupp.sum
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [he] at hn
    linarith
  · exact hupper g hg

end Hindman168.FiniteMass
