import Hindman168.SelectedAlignmentSourceKeyRecipeFamily
import Hindman168.AlignmentJointObservableCompactness

/-! Uniform limits of the selected key recipes control the literal padding
piece models on the same original joint orbit, uniformly in every permitted
query and every integer pivot point of the good cell. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

theorem selected_alignment_key_frozen_readings_uniform
    {ι : Type} [Fintype ι] {n M s : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (F : MasterParameterFamily) (q₀ C : ℕ) (T : ι → Finset (Fin n))
    (V U : ι → Finset (AlignmentAddingPair n i → ℤ)) (hzero : ∀ ν, 0 ∈ U ν)
    (stored : ι → AlignmentAddingPair n i → ℤ) (hstored : ∀ ν, stored ν ∈ V ν)
    (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
    (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G)
    (W : ℕ → ℕ) (x : ℕ → Fin M → ℕ)
    (hxs : ∀ᶠ m in atTop, x m ∈ (globalRawMass (F.cutoff (W m)) (primorial (W m)) M).support)
    (hgood : ∀ᶠ m in atTop, ∀ ν,
      selectedAlignmentFullExposureArrayStable F e heM i q₀ (W m) C (T ν) (V ν) (U ν) (x m))
    (limit : ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ))
    (hconv : ∀ ν, TendstoUniformly
      (fun m => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U stored obs (W m)
        (selectedAlignmentSourceKey F e heM i (W m) (T ν) (x m)) ν) (limit ν) atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ ν, ∀ query ∈ U ν, ∀ p ell : ℤ,
      Int.ModEq (F.modulus (W m):ℕ) p (x m (principalAlignmentEmbedding e heM i)) →
      |p + (F.modulus (W m):ℤ)*ell-x m (principalAlignmentEmbedding e heM i)| ≤
        (C*selectedPrincipalMicrocellWidth F e (W m) i:ℕ) →
      let key := fun k => selectedAlignmentSourceKey F e heM i (W m) (T k) (x m)
      |piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
        (obs ν) (g ν) (a ν) (W m)
        (alignmentIntegerArrayArgument (x m) (F.modulus (W m))
          (fun b => alignmentPairResidue q₀ (W m) (F.modulus (W m)) b (x m))
          (fun b => alignmentPairProgression q₀ (W m) (F.modulus (W m)) b (x m))
          ((T ν).image (principalAlignmentEmbedding e heM)) (p+(F.modulus (W m):ℤ)*ell)
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (stored ν))
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query)) -
        limit ν (alignmentJointNativeCosetEvaluation D r v hv ν
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query)
          (QuotientGroup.mk (alignmentOriginalJointPointOrbit D r v hv F q₀ (W m)
            (fun k => (T k).image (principalAlignmentEmbedding e heM)) (x m) p
            (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (stored k))
            (fun k => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U stored g (W m) (key k) k)
            (fun k => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U stored a (W m) (key k) k) ell)))| < ε := by
  have he : ∀ ν, ∀ᶠ m in atTop, ∀ z,
      |selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U stored obs (W m)
        (selectedAlignmentSourceKey F e heM i (W m) (T ν) (x m)) ν z - limit ν z| < ε := by
    intro ν
    simpa only [Real.dist_eq, abs_sub_comm] using
      (Metric.tendstoUniformly_iff.mp (hconv ν)) ε hε
  filter_upwards [Filter.eventually_all.mpr he, hxs, hgood] with m hm hx hg
  intro ν query hquery p ell hp hdist
  dsimp only
  rw [selected_alignment_key_recipe_native_joint_reading e heM i D r v hv F q₀ (W m) C T ν
    V U hzero (x m) (x m) hx (alignmentGlobalRawMass_support_coprime F (W m) (x m) hx)
    (fun k _ => selected_alignment_full_raw_support_cutoff F (W m) (x m) hx
      (principalAlignmentEmbedding e heM k)) rfl hg stored hstored query hquery p ell hp hdist obs g a]
  exact hm ν _

end Hindman168
