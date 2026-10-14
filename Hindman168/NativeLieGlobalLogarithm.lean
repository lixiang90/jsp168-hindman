import Hindman168.NativeLieExponentialCovering
import Mathlib.Topology.Homotopy.Lifting

/-! The original simply connected group has a genuine continuous global
logarithm. Its actual local path connectedness follows from the already
proved original quotient map. The genuine covering lifting theorem lifts
the identity map of the whole original group, with value zero at one. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieGlobalLogarithm_exists :
    ∃ L : C(G, E), L 1 = 0 ∧
      ∀ g : G, nativeLieExponential (I := I) (G := G) (L g) = g := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have cov : IsCoveringMap exp := nativeLieExponential_isCoveringMap (I := I) (G := G)
  letI : LocallyPathConnectedSpace G :=
    (nativeLieExponential_isQuotientMap (E := E) (I := I) (G := G)).locallyPathConnectedSpace
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    (ContinuousMap.id G) (1 : G) (0 : E) (nativeLieExponential_zero (I := I) (G := G))
  exact ⟨L, hL0, fun g => congrFun hL g⟩

noncomputable def nativeLieGlobalLogarithm : C(G, E) :=
  Classical.choose (nativeLieGlobalLogarithm_exists (E := E) (I := I) (G := G))

 theorem nativeLieGlobalLogarithm_one :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) 1 = 0 :=
  (Classical.choose_spec (nativeLieGlobalLogarithm_exists (E := E) (I := I) (G := G))).1

 theorem nativeLieExponential_globalLogarithm (g : G) :
    nativeLieExponential (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = g :=
  (Classical.choose_spec (nativeLieGlobalLogarithm_exists (E := E) (I := I) (G := G))).2 g

 theorem nativeLieGlobalLogarithm_exponential (v : E) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) v) = v := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let L : C(G, E) := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  have cov : IsCoveringMap exp := nativeLieExponential_isCoveringMap (I := I) (G := G)
  have he : exp ∘ (L ∘ exp) = exp ∘ (id : E → E) := by
    funext u
    exact nativeLieExponential_globalLogarithm (I := I) (exp u)
  have h0 : (L ∘ exp) 0 = (id : E → E) 0 := by
    have hz : exp 0 = 1 := nativeLieExponential_zero (I := I) (G := G)
    change L (exp 0) = 0
    rw [hz]
    exact nativeLieGlobalLogarithm_one (I := I) (G := G)
  have h := cov.eq_of_comp_eq (L.continuous.comp cov.continuous) continuous_id he (0 : E) h0
  exact congrFun h v

 theorem nativeLieExponential_injective :
    Injective (fun v : E => nativeLieExponential (I := I) (G := G) v) := by
  intro v w h
  have he := congrArg (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) h
  simpa only [nativeLieGlobalLogarithm_exponential] using he

 theorem nativeLieExponentialPeriods_eq_bot :
    nativeLieExponentialPeriods (E := E) (I := I) (G := G) = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    apply nativeLieExponential_injective (I := I) (G := G)
    exact hv.trans (nativeLieExponential_zero (I := I) (G := G)).symm
  · exact bot_le

end Hindman168
