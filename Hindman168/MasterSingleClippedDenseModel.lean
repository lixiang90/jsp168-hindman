import Hindman168.MasterSingleClippedConvexTests
import Hindman168.FiniteDenseModelSeparation

/-!
# Actual bounded dense models for a fixed original local template

All polynomial and positive-part limits are derived from the original-law
uniform product theorem. Minimax supplies one model for every admissible
input of this template simultaneously. Multiple original template types and
the paper's full diagonal construction still require separate instantiation.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem signedOriginalSingleClippedClass_abs_le {a d N K m : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (cut : ℝ) (hcut : 0 ≤ cut) (w : ℕ) {f : ℤ → ℝ}
    (hf : f ∈ signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w) :
    ∀ y, |f y| ≤ cut := by
  obtain ⟨sign, u, hs, _, rfl⟩ := hf
  intro y
  rw [abs_mul, hs, one_mul]
  exact predictionClip_abs_le hcut

theorem signedOriginalSingleClippedClass_neg {a d N K m : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (cut : ℝ) (w : ℕ) {f : ℤ → ℝ}
    (hf : f ∈ signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w) :
    -f ∈ signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w := by
  obtain ⟨sign, u, hs, hu, rfl⟩ := hf
  refine ⟨-sign, u, by simpa only [abs_neg] using hs, hu, ?_⟩
  funext y
  simp only [Pi.neg_apply, neg_mul]

theorem signedOriginalSingleClippedClass_nonempty {a d N K m : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (cut : ℝ) (w : ℕ) (hν : ∀ y, 0 ≤ masterPredictionBlockMask F C label w y) :
    (signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w).Nonempty := by
  let u : OriginalSingleDualInput a d := ⟨fun _ => 0, fun _ _ _ => 0⟩
  have hu : u.Admissible F C label w := by
    constructor
    · intro x; norm_num [u]
    · intro x S y
      change |(0 : ℝ)| ≤ 1 + masterPredictionBlockMask F C label w y
      rw [abs_zero]
      exact add_nonneg zero_le_one (hν y)
  exact ⟨_, 1, u, abs_one, hu, rfl⟩

theorem MasterParameterConditions.uniform_single_hull_positive_part
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
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ G ∈ closedConvexHull ℝ (signedOriginalSingleClippedClass (a := a) (d := d)
        F C label gap J choice tests den cut w),
      |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (masterPredictionBlockMask F C label w y - 1) * max (G y) 0)| < η := by
  have hμ : ∀ᶠ w in atTop, ∀ y, 0 ≤ integerMass (F.cutoff w (root w).val) (primorial w) y :=
    hF.raw_cutoffs_valid.mono (fun w hw => integerMass_nonneg
      (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
  have hc : ∀ᶠ w in atTop, ∀ y, |masterPredictionBlockMask F C label w y - 1| ≤
      1 + masterPredictionBlockMask F C label w y :=
    (hF.block_mask_eventually_nonneg C hN label).mono
      (fun _ hw y => centered_mask_abs_le_one_add (hw y))
  have hcut0 : 0 ≤ cut := (zero_le_one.trans (predictionDualThreshold_ge_one d)).trans hcut.le
  exact uniform_positive_part_closedConvexHull
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => masterPredictionBlockMask F C label w y - 1)
    (fun w y => 1 + masterPredictionBlockMask F C label w y)
    (fun w => signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w)
    cut 3 hμ hc (by norm_num)
    (hF.dual_weighted_root_mass_eventually_le C hN label tail htail root htailroot)
    (Eventually.of_forall (fun w _ hf => signedOriginalSingleClippedClass_abs_le
      F C label gap J choice tests den cut hcut0 w hf))
    (hF.uniform_single_clipped_hull_polynomial hD hd C hN label tail htail root gap
      htailroot htailgap hgap J hJ choice tests den hden masterSlot hmasterSlot hinclude cut hcut)

theorem MasterParameterConditions.uniform_single_clipped_dense_models
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
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ ρ : ℤ → ℝ,
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ masterPredictionBlockMask F C label w y) →
      ∃ model : ℤ → ℝ, (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
        ∀ g ∈ signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w,
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ y - model y) * g y)| < η := by
  intro η hη
  have hpos := hF.uniform_single_hull_positive_part hD hd C hN label tail htail root gap
    htailroot htailgap hgap J hJ choice tests den hden masterSlot hmasterSlot hinclude cut hcut
    (η / 2) (by positivity)
  filter_upwards [hpos, hF.block_mask_eventually_nonneg C hN label, hF.raw_cutoffs_valid]
    with w hpw hnw hrw
  intro ρ hρ
  let S := signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w
  have hcut0 : 0 ≤ cut := (zero_le_one.trans (predictionDualThreshold_ge_one d)).trans hcut.le
  obtain ⟨model, hm, he⟩ := bounded_dense_model_of_positive_part
    (integerMass (F.cutoff w (root w).val) (primorial w))
    (integerMass_nonneg (hrw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
    ρ (masterPredictionBlockMask F C label w) hρ S
    (signedOriginalSingleClippedClass_nonempty F C label gap J choice tests den cut w hnw)
    cut (fun _ hg => signedOriginalSingleClippedClass_abs_le F C label gap J choice tests den cut hcut0 w hg)
    (fun _ hg => signedOriginalSingleClippedClass_neg F C label gap J choice tests den cut w hg)
    (η / 2) (fun G hG => (le_abs_self _).trans (hpw G hG).le)
  exact ⟨model, hm, fun g hg => (he g hg).trans_lt (by linarith)⟩

end Hindman168
