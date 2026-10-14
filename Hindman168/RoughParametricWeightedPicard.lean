import Hindman168.RoughParametricWeightedDegree

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : ℕ → Submodule ℝ E) (hF : Antitone F)
  (B : E →L[ℝ] (E →L[ℝ] E))
  (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))

include hF hB

theorem rough_parametric_weighted_bilinear_same {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) :
    RoughParametricWeightedDegree F (roughParametricBilinear B p q) k :=
  rough_parametric_weighted_mono F hF
    (rough_parametric_weighted_bilinear F hF B hB hp hq) (Nat.le_add_right k k)

theorem rough_parametric_weighted_ad {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) (n : ℕ) :
    RoughParametricWeightedDegree F (roughParametricAd B p q n) k := by
  induction n with
  | zero => exact hq
  | succ n ih => exact rough_parametric_weighted_bilinear_same F hF B hB hp ih

theorem rough_parametric_weighted_defect (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) :
    RoughParametricWeightedDegree F (roughParametricDefect B s p q) k := by
  apply rough_parametric_weighted_sum
  intro n _
  apply rough_parametric_weighted_scale
  exact rough_parametric_weighted_ad F hF B hB hp hq (n+1)

theorem rough_parametric_weighted_defect_power (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) (n : ℕ) :
    RoughParametricWeightedDegree F (roughParametricDefectPower B s p q n) k := by
  induction n with
  | zero => exact hq
  | succ n ih => exact rough_parametric_weighted_defect F hF B hB s hp ih

theorem rough_parametric_weighted_field (s : ℕ) {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) :
    RoughParametricWeightedDegree F (roughParametricField B s p q) k := by
  apply rough_parametric_weighted_sum
  intro n _
  exact rough_parametric_weighted_defect_power F hF B hB s hp hq n

theorem rough_parametric_weighted_picard (s : ℕ) {w u : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hw : RoughVectorMvWeightedDegree F w k) (hu : RoughVectorMvWeightedDegree F u k) (n : ℕ) :
    RoughParametricWeightedDegree F (roughParametricPicard B s w u n) k := by
  induction n with
  | zero => exact rough_parametric_weighted_singleton F hu 0
  | succ n ih =>
      exact rough_parametric_weighted_append F (rough_parametric_weighted_singleton F hu 0)
        (rough_parametric_weighted_primitive F (rough_parametric_weighted_field F hF B hB s ih
          (rough_parametric_weighted_singleton F hw 0)))

end Hindman168
