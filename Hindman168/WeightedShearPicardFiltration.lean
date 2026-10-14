import Hindman168.RoughParametricPicardPerturbation
import Hindman168.WeightedShearPolynomial

/-! Coordinate-weighted coefficient control for the actual finite Picard
product and its exact perturbation polynomial.  This uses the original
filtration and arbitrary coordinate weights, rather than replacing them by
ordinary degree or by a stretched lower-central filtration. -/
namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {weights : σ → ℕ}

def AffineShearWeightedVector (weights : σ → ℕ) (F : ℕ → Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (k : ℕ) : Prop :=
  ∀ a ∈ p, a.2 ∈ F (a.1.weightedTotalDegree weights + k)

def AffineShearWeightedCurve (weights : σ → ℕ) (F : ℕ → Submodule ℝ E)
    (p : RoughParametricCurve σ E) (k : ℕ) : Prop :=
  ∀ a ∈ p, AffineShearWeightedVector weights F a.2 k

 theorem affineShear_weightedTotalDegree_mul (weights : σ → ℕ)
    (p q : MvPolynomial σ ℝ) :
    (p*q).weightedTotalDegree weights ≤ p.weightedTotalDegree weights + q.weightedTotalDegree weights := by
  classical
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q ha)
  rw [map_add]
  exact add_le_add (Finset.le_sup hb) (Finset.le_sup hc)

theorem affineShear_rough_vector_weighted_append (F : ℕ → Submodule ℝ E)
    {p q : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : AffineShearWeightedVector weights F p k) (hq : AffineShearWeightedVector weights F q k) :
    AffineShearWeightedVector weights F (p++q) k :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem affineShear_rough_vector_weighted_scale (F : ℕ → Submodule ℝ E) (r : ℝ)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : AffineShearWeightedVector weights F p k) :
    AffineShearWeightedVector weights F (roughVectorMvScale r p) k := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (F (b.1.weightedTotalDegree weights+k)).smul_mem r (hp b hb)

theorem affineShear_rough_vector_weighted_bilinear (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p q : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hp : AffineShearWeightedVector weights F p k) (hq : AffineShearWeightedVector weights F q l) :
    AffineShearWeightedVector weights F (roughVectorMvBilinear B p q) (k+l) := by
  rintro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  apply hF _ (hB _ _ _ _ (hp b hb) (hq c hc))
  have hd := affineShear_weightedTotalDegree_mul weights b.1 c.1
  dsimp
  omega

theorem affineShear_rough_vector_weighted_mono (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hp : AffineShearWeightedVector weights F p l) (hkl : k ≤ l) :
    AffineShearWeightedVector weights F p k :=
  fun a ha => hF (Nat.add_le_add_left hkl (a.1.weightedTotalDegree weights)) (hp a ha)

theorem affineShear_rough_parametric_weighted_mono (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughParametricCurve σ E} {k l : ℕ}
    (hp : AffineShearWeightedCurve weights F p l) (hkl : k ≤ l) :
    AffineShearWeightedCurve weights F p k :=
  fun a ha => affineShear_rough_vector_weighted_mono F hF (hp a ha) hkl

theorem affineShear_rough_parametric_weighted_singleton (F : ℕ → Submodule ℝ E)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : AffineShearWeightedVector weights F p k) (n : ℕ) :
    AffineShearWeightedCurve weights F [(n,p)] k := by
  intro a ha
  exact List.mem_singleton.mp ha ▸ hp

theorem affineShear_rough_parametric_weighted_append (F : ℕ → Submodule ℝ E)
    {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) :
    AffineShearWeightedCurve weights F (p++q) k :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem affineShear_rough_parametric_weighted_sum (F : ℕ → Submodule ℝ E) (n k : ℕ)
    (p : ℕ → RoughParametricCurve σ E) (hp : ∀ j < n, AffineShearWeightedCurve weights F (p j) k) :
    AffineShearWeightedCurve weights F (roughParametricSum n p) k := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  exact hp j (List.mem_range.mp hj) a ha

theorem affineShear_rough_parametric_weighted_endpoint (F : ℕ → Submodule ℝ E)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : AffineShearWeightedCurve weights F p k) :
    AffineShearWeightedVector weights F (roughParametricEndpoint p) k := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  exact hp b hb a ha

theorem affineShear_rough_parametric_weighted_scale (F : ℕ → Submodule ℝ E) (r : ℚ)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : AffineShearWeightedCurve weights F p k) :
    AffineShearWeightedCurve weights F (roughParametricScale r p) k := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact affineShear_rough_vector_weighted_scale F _ (hp b hb)

theorem affineShear_rough_parametric_weighted_primitive (F : ℕ → Submodule ℝ E)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : AffineShearWeightedCurve weights F p k) :
    AffineShearWeightedCurve weights F (roughParametricPrimitive p) k := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact affineShear_rough_vector_weighted_scale F _ (hp b hb)

theorem affineShear_rough_parametric_weighted_bilinear (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p q : RoughParametricCurve σ E} {k l : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q l) :
    AffineShearWeightedCurve weights F (roughParametricBilinear B p q) (k+l) := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact affineShear_rough_vector_weighted_bilinear F hF B hB (hp b hb) (hq c hc)

section Picard
variable (F : ℕ → Submodule ℝ E) (hF : Antitone F)
  (B : E →L[ℝ] (E →L[ℝ] E))
  (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
include hF hB

theorem affineShear_rough_parametric_weighted_bilinear_same {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) :
    AffineShearWeightedCurve weights F (roughParametricBilinear B p q) k :=
  affineShear_rough_parametric_weighted_mono F hF
    (affineShear_rough_parametric_weighted_bilinear F hF B hB hp hq) (Nat.le_add_right k k)

theorem affineShear_rough_parametric_weighted_ad {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) (n : ℕ) :
    AffineShearWeightedCurve weights F (roughParametricAd B p q n) k := by
  induction n with
  | zero => exact hq
  | succ n ih => exact affineShear_rough_parametric_weighted_bilinear_same F hF B hB hp ih

theorem affineShear_rough_parametric_weighted_defect (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) :
    AffineShearWeightedCurve weights F (roughParametricDefect B s p q) k := by
  apply affineShear_rough_parametric_weighted_sum
  intro n _
  apply affineShear_rough_parametric_weighted_scale
  exact affineShear_rough_parametric_weighted_ad F hF B hB hp hq (n+1)

theorem affineShear_rough_parametric_weighted_defect_power (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) (n : ℕ) :
    AffineShearWeightedCurve weights F (roughParametricDefectPower B s p q n) k := by
  induction n with
  | zero => exact hq
  | succ n ih => exact affineShear_rough_parametric_weighted_defect F hF B hB s hp ih

theorem affineShear_rough_parametric_weighted_field (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : AffineShearWeightedCurve weights F p k) (hq : AffineShearWeightedCurve weights F q k) :
    AffineShearWeightedCurve weights F (roughParametricField B s p q) k := by
  apply affineShear_rough_parametric_weighted_sum
  intro n _
  exact affineShear_rough_parametric_weighted_defect_power F hF B hB s hp hq n

theorem affineShear_rough_parametric_weighted_picard (s : ℕ) {w u : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hw : AffineShearWeightedVector weights F w k) (hu : AffineShearWeightedVector weights F u k) (n : ℕ) :
    AffineShearWeightedCurve weights F (roughParametricPicard B s w u n) k := by
  induction n with
  | zero => exact affineShear_rough_parametric_weighted_singleton F hu 0
  | succ n ih =>
      exact affineShear_rough_parametric_weighted_append F (affineShear_rough_parametric_weighted_singleton F hu 0)
        (affineShear_rough_parametric_weighted_primitive F (affineShear_rough_parametric_weighted_field F hF B hB s ih
          (affineShear_rough_parametric_weighted_singleton F hw 0)))


end Picard

theorem affineShear_rough_parametric_bilinear_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p₀ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp : AffineShearWeightedCurve weights F p₀ k) (hq : AffineShearWeightedCurve weights F q₁ k)
    (hdp : AffineShearWeightedCurve weights F dp l) (hdq : AffineShearWeightedCurve weights F dq l) :
    AffineShearWeightedCurve weights F (roughParametricBilinearPerturbation B p₀ dp q₁ dq) l := by
  apply affineShear_rough_parametric_weighted_append
  · exact affineShear_rough_parametric_weighted_mono F hF
      (affineShear_rough_parametric_weighted_bilinear F hF B hB hdp hq) (Nat.le_add_right l k)
  · exact affineShear_rough_parametric_weighted_mono F hF
      (affineShear_rough_parametric_weighted_bilinear F hF B hB hp hdq) (Nat.le_add_left l k)

theorem affineShear_rough_parametric_ad_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : AffineShearWeightedCurve weights F p₀ k) (hp₁ : AffineShearWeightedCurve weights F p₁ k)
    (hq₁ : AffineShearWeightedCurve weights F q₁ k)
    (hdp : AffineShearWeightedCurve weights F dp l) (hdq : AffineShearWeightedCurve weights F dq l)
    (n : ℕ) : AffineShearWeightedCurve weights F (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq n) l := by
  induction n with
  | zero => exact hdq
  | succ n ih =>
      exact affineShear_rough_parametric_bilinear_perturbation_weighted F hF B hB hp₀
        (affineShear_rough_parametric_weighted_ad F hF B hB hp₁ hq₁ n) hdp ih

theorem affineShear_rough_parametric_defect_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : AffineShearWeightedCurve weights F p₀ k) (hp₁ : AffineShearWeightedCurve weights F p₁ k)
    (hq₁ : AffineShearWeightedCurve weights F q₁ k)
    (hdp : AffineShearWeightedCurve weights F dp l) (hdq : AffineShearWeightedCurve weights F dq l) :
    AffineShearWeightedCurve weights F (roughParametricDefectPerturbation B s p₀ p₁ dp q₁ dq) l := by
  apply affineShear_rough_parametric_weighted_sum
  intro n _
  apply affineShear_rough_parametric_weighted_scale
  exact affineShear_rough_parametric_ad_perturbation_weighted F hF B hB hp₀ hp₁ hq₁ hdp hdq (n+1)

theorem affineShear_rough_parametric_defect_power_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : AffineShearWeightedCurve weights F p₀ k) (hp₁ : AffineShearWeightedCurve weights F p₁ k)
    (hq₁ : AffineShearWeightedCurve weights F q₁ k)
    (hdp : AffineShearWeightedCurve weights F dp l) (hdq : AffineShearWeightedCurve weights F dq l)
    (n : ℕ) :
    AffineShearWeightedCurve weights F (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq n) l := by
  induction n with
  | zero => exact hdq
  | succ n ih =>
      exact affineShear_rough_parametric_defect_perturbation_weighted F hF B hB s hp₀ hp₁
        (affineShear_rough_parametric_weighted_defect_power F hF B hB s hp₁ hq₁ n) hdp ih

theorem affineShear_rough_parametric_field_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : AffineShearWeightedCurve weights F p₀ k) (hp₁ : AffineShearWeightedCurve weights F p₁ k)
    (hq₁ : AffineShearWeightedCurve weights F q₁ k)
    (hdp : AffineShearWeightedCurve weights F dp l) (hdq : AffineShearWeightedCurve weights F dq l) :
    AffineShearWeightedCurve weights F (roughParametricFieldPerturbation B s p₀ p₁ dp q₁ dq) l := by
  apply affineShear_rough_parametric_weighted_sum
  intro n _
  exact affineShear_rough_parametric_defect_power_perturbation_weighted F hF B hB s hp₀ hp₁ hq₁ hdp hdq n

theorem affineShear_rough_parametric_picard_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {w₀ w₁ dw u₀ u₁ du : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hw₀ : AffineShearWeightedVector weights F w₀ k) (hw₁ : AffineShearWeightedVector weights F w₁ k)
    (hu₀ : AffineShearWeightedVector weights F u₀ k) (hu₁ : AffineShearWeightedVector weights F u₁ k)
    (hdw : AffineShearWeightedVector weights F dw l) (hdu : AffineShearWeightedVector weights F du l) (n : ℕ) :
    AffineShearWeightedCurve weights F (roughParametricPicardPerturbation B s w₀ w₁ dw u₀ u₁ du n) l := by
  induction n with
  | zero => exact affineShear_rough_parametric_weighted_singleton F hdu 0
  | succ n ih =>
      apply affineShear_rough_parametric_weighted_append F (affineShear_rough_parametric_weighted_singleton F hdu 0)
      apply affineShear_rough_parametric_weighted_primitive
      exact affineShear_rough_parametric_field_perturbation_weighted F hF B hB s
        (affineShear_rough_parametric_weighted_picard F hF B hB s hw₀ hu₀ n)
        (affineShear_rough_parametric_weighted_picard F hF B hB s hw₁ hu₁ n)
        (affineShear_rough_parametric_weighted_singleton F hw₁ 0) ih (affineShear_rough_parametric_weighted_singleton F hdw 0)

end Hindman168
