import Hindman168.NativeLieGroupLowerCentralComparison

/-! The actual global logarithm of an original product equals the
genuine finite Picard product logarithm. Its additive errors lie in the
proved original native layers. This is a triangular comparison, not a
claim of rational BCH coefficients or of equality of the two series. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieGlobalLogarithm_product_exponentials (u w : E) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) =
        nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1 := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let z : E := nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1
  have he : exp z = exp u * exp w := nativeLieExponential_product_logarithm (E := E) u w
  change log (exp u * exp w) = z
  rw [← he]
  exact nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G) z

 theorem nativeLieGlobalLogarithm_product_lowerCentral
    (u : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) -
        (u + w) ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  rw [nativeLieGlobalLogarithm_product_exponentials]
  simpa only [one_smul] using nativeLieLogarithmLift_sub_affine_lowerCentral hw u 1

 theorem nativeLieGlobalLogarithm_mul_add_mod_commutatorLayer (g h : G) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g * h) -
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g +
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈
          nativeLieLowerCentralModel (I := I) (G := G) 1 := by
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have hg : exp (log g) = g := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g
  have hh : exp (log h) = h := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) h
  have hw : log h ∈ nativeLieLowerCentralModel (I := I) (G := G) 0 := by
    rw [nativeLieLowerCentralModel_zero]
    trivial
  have hp := nativeLieGlobalLogarithm_product_lowerCentral (E := E) (I := I) (G := G) (log g) hw
  change log (exp (log g) * exp (log h)) - (log g + log h) ∈ _ at hp
  rw [hg, hh] at hp
  exact hp

 theorem nativeGroupLowerCentralSeries_log_mem (j : ℕ) {g : G}
    (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeLieLowerCentralModel (I := I) (G := G) j :=
    (nativeLieLowerCentralSubgroup_mem_globalLogarithm_iff (E := E) (I := I) (G := G) j g).mp
      (nativeGroupLowerCentralSeries_le_exponential (E := E) (I := I) (G := G) j hg)

end Hindman168
