import Hindman168.HarmonicDilation
import Hindman168.FiniteProbability

/-!
# Finite product-sampling comparison with explicit error

The tail product may have any finite probability distribution rho supported
on positive W-units at most K. It is sampled independently of a harmonic
pivot Y. The law of sigma*Y is compared to mu(y)*E[sigma*1_{sigma|y}].
The comparison remains unnormalized; its mass error is retained separately.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def productMass (ρ : FiniteMass.Mass ℕ) (X W : ℕ) : FiniteMass.Mass ℕ :=
  FiniteMass.mixture ρ.support (fun k => ρ k) (fun k => (rawMass X W).mapDomain (fun n => k * n))

noncomputable def productComparisonMass (ρ : FiniteMass.Mass ℕ) (X W : ℕ) : FiniteMass.Mass ℕ :=
  FiniteMass.mixture ρ.support (fun k => ρ k) (fun k => etaMass X W k)

noncomputable def divisorMask (ρ : FiniteMass.Mass ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ ρ.support, ρ k * (if k ∣ n then (k : ℝ) else 0)

theorem productComparisonMass_apply (ρ : FiniteMass.Mass ℕ) (X W n : ℕ) :
    productComparisonMass ρ X W n = harmonicWeight X W n * divisorMask ρ n := by
  classical
  rw [productComparisonMass, FiniteMass.mixture_apply, divisorMask, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [etaMass_apply]
  split_ifs <;> ring

theorem productMass_nonneg {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (hZ : 0 < harmonicNormalizer X W) (n : ℕ) :
    0 ≤ productMass ρ X W n := by
  apply FiniteMass.mixture_nonneg (fun k _ => hρ k)
  intro k _ n
  exact FiniteMass.push_nonneg (rawMass X W) (fun n => k * n)
    (fun n => by rw [rawMass_apply]; exact harmonicWeight_nonneg hZ n) n

theorem productComparisonMass_nonneg {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (hZ : 0 < harmonicNormalizer X W) (n : ℕ) :
    0 ≤ productComparisonMass ρ X W n :=
  FiniteMass.mixture_nonneg (fun k _ => hρ k) (fun k _ n => etaMass_nonneg hZ k n) n

theorem productMass_total {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (htρ : FiniteMass.total ρ = 1) (hZ : 0 < harmonicNormalizer X W) :
    FiniteMass.total (productMass ρ X W) = 1 := by
  rw [productMass, FiniteMass.mixture_total]
  simp only [FiniteMass.total_push, rawMass_total hZ, mul_one]
  exact htρ

theorem productMass_support {ρ : FiniteMass.Mass ℕ} {X W k : ℕ}
    (hk : k ∈ (productMass ρ X W).support) :
    ∃ s ∈ ρ.support, ∃ n ∈ harmonicWindow X W, s * n = k := by
  classical
  obtain ⟨s, hs, hks⟩ := Finsupp.mem_support_finsetSum k hk
  have hp : k ∈ ((rawMass X W).mapDomain (fun n => s * n)).support :=
    Finsupp.support_smul hks
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
  have hw : n ∈ harmonicWindow X W := by
    have h := intervalMass_support X (X ^ 2 : ℕ) W (harmonicNormalizer X W) hn
    rwa [unitInterval_raw] at h
  exact ⟨s, hs, n, hw, he⟩

theorem harmonicPMF_eq_toPMF {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) :
    harmonicPMF X W hZ = FiniteMass.toPMF (rawMass X W)
      (fun n => by rw [rawMass_apply]; exact harmonicWeight_nonneg hZ n) (rawMass_total hZ) := by
  ext n
  rw [harmonicPMF_apply, FiniteMass.toPMF_apply, rawMass_apply]

/-- Independent tail-product and pivot sampling, as an actual PMF. -/
noncomputable def productPMF (ρ : FiniteMass.Mass ℕ) (hρ : ∀ k, 0 ≤ ρ k)
    (htρ : FiniteMass.total ρ = 1) (X W : ℕ) (hZ : 0 < harmonicNormalizer X W) : PMF ℕ :=
  (FiniteMass.toPMF ρ hρ htρ).bind (fun k => (harmonicPMF X W hZ).map (fun n => k * n))

theorem productPMF_apply {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1)
    (hZ : 0 < harmonicNormalizer X W) (n : ℕ) :
    productPMF ρ hρ htρ X W hZ n = ENNReal.ofReal (productMass ρ X W n) := by
  unfold productPMF
  rw [harmonicPMF_eq_toPMF hZ]
  simp_rw [FiniteMass.toPMF_map]
  exact FiniteMass.toPMF_bind_apply ρ hρ htρ
    (fun k => (rawMass X W).mapDomain (fun n => k * n))
    (fun k => FiniteMass.push_nonneg _ _
      (fun n => by rw [rawMass_apply]; exact harmonicWeight_nonneg hZ n))
    (fun _ => by rw [FiniteMass.total_push, rawMass_total hZ]) n

theorem productPMF_eq_toPMF {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1)
    (hZ : 0 < harmonicNormalizer X W) :
    productPMF ρ hρ htρ X W hZ = FiniteMass.toPMF (productMass ρ X W)
      (productMass_nonneg hρ hZ) (productMass_total htρ hZ) := by
  ext n
  rw [productPMF_apply, FiniteMass.toPMF_apply]

theorem dilationError_mono {X W k K : ℕ} (hX : 2 ≤ X) (hk : 0 < k) (hkK : k ≤ K)
    (hlog : (W : ℝ) / X < Real.log X) : dilationError X W k ≤ dilationError X W K := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
  have hlogs := Real.log_le_log hkR hkKR
  have hf : 0 ≤ 1 + 1 / (X : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hkKR (show (0 : ℝ) ≤ W from Nat.cast_nonneg W)
  have hdiv := div_le_div_of_nonneg_right hmul hXR.le
  have hterm := mul_le_mul_of_nonneg_right hdiv hf
  unfold dilationError
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hlog).le
  linarith

theorem residueError_mono {X W k K : ℕ} (hX : 2 ≤ X) (hkK : k ≤ K)
    (hlog : (W : ℝ) / X < Real.log X) : residueError X W k ≤ residueError X W K := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  unfold residueError
  apply div_le_div_of_nonneg_right _ (mul_pos hXR (sub_pos.mpr hlog)).le
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg W)
  exact_mod_cast Nat.add_le_add_right hkK 1

/-- The quantitative finite version of conditioning on the tail product. -/
theorem product_law_error {ρ : FiniteMass.Mass ℕ} {X W K : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1) (hX : 2 ≤ X) (hW : 0 < W)
    (hKX : K ≤ X) (hs : ∀ k ∈ ρ.support, 0 < k ∧ k ≤ K ∧ W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    FiniteMass.distance (productMass ρ X W) (productComparisonMass ρ X W) ≤
      dilationError X W K := by
  apply FiniteMass.mixture_distance_uniform _ _ (fun k _ => hρ k) htρ
  intro k hk
  obtain ⟨hkpos, hkK, hco⟩ := hs k hk
  exact (harmonic_dilation_error hX hW hkpos (hkK.trans hKX) hco hlog).trans
    (dilationError_mono hX hkpos hkK hlog)

theorem product_comparison_mass_error {ρ : FiniteMass.Mass ℕ} {X W K : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1) (hX : 2 ≤ X) (hW : 0 < W)
    (hs : ∀ k ∈ ρ.support, 0 < k ∧ k ≤ K ∧ W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    |FiniteMass.total (productComparisonMass ρ X W) - 1| ≤ residueError X W K := by
  apply FiniteMass.mixture_mass_error _ (fun k _ => hρ k) htρ
  intro k hk
  obtain ⟨hkpos, hkK, hco⟩ := hs k hk
  exact (etaMass_mass_error hX hW hkpos hco hlog).trans (residueError_mono hX hkK hlog)

end Hindman168
