import Hindman168.NilCornerUniformRecipes
import Mathlib.Topology.Homeomorph.Lemmas

/-! Continuous missing-corner reconstruction from an independently
proved uniqueness certificate on a genuine compact set of full cubes.
No nilpotent cube uniqueness or Lie-theoretic compactness is assumed
silently: both remain explicit hypotheses in this topological step. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal

variable {ι X : Type*}

def cornerDelete (c : Option ι → X) : ι → X := fun j => c (some j)

theorem cornerDelete_continuous [TopologicalSpace X] : Continuous (cornerDelete (ι := ι) (X := X)) := by
  exact continuous_pi (fun j => continuous_apply (some j))

def CornerUnique (K : Set (Option ι → X)) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, (∀ j, x (some j) = y (some j)) → x none = y none

theorem cornerDelete_injective_on_cubes (K : Set (Option ι → X)) (hK : CornerUnique K) :
    Function.Injective (fun x : K => cornerDelete x.val) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  cases j with
  | none => exact hK x.val x.property y.val y.property (congrFun hxy)
  | some j => exact congrFun hxy j

theorem compactCorner_continuous_reconstruction [TopologicalSpace X] [T2Space X]
    (K : Set (Option ι → X)) (hcompact : IsCompact K) (hunique : CornerUnique K) :
    ∃ R : C(Set.range (fun x : K => cornerDelete x.val), X),
      ∀ x : K, R ⟨cornerDelete x.val, ⟨x, rfl⟩⟩ = x.val none := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let del : K → (ι → X) := fun x => cornerDelete x.val
  have hdel : Continuous del := cornerDelete_continuous.comp continuous_subtype_val
  let emb := hdel.isClosedEmbedding (cornerDelete_injective_on_cubes K hunique)
  let e : K ≃ₜ Set.range del := emb.toIsEmbedding.toHomeomorph
  let root : C(K, X) := ⟨fun x => x.val none, (continuous_apply none).comp continuous_subtype_val⟩
  refine ⟨root.comp ⟨e.symm, e.symm.continuous⟩, ?_⟩
  intro x
  change root (e.symm ⟨del x, ⟨x, rfl⟩⟩) = _
  have hx : e x = ⟨del x, ⟨x, rfl⟩⟩ := by rfl
  rw [← hx, e.symm_apply_apply]
  rfl

noncomputable def CornerProductRecipe.value [TopologicalSpace X] [Fintype ι] (r : CornerProductRecipe ι X)
    (v : ι → X) : ℝ :=
  (r.map (fun t => t.1 * ∏ j, t.2 j (v j))).sum

theorem cornerRecipe_eval_eq_value [TopologicalSpace X] [Fintype ι] {K : Type*} [TopologicalSpace K]
    (r : CornerProductRecipe ι X) (vertex : ι → C(K, X)) (x : K) :
    r.eval vertex x = r.value (fun j => vertex j x) := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    simp only [CornerProductRecipe.eval, CornerProductRecipe.value, List.map_cons,
      List.sum_cons, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul, cornerCoordinateProduct_apply] at ih ⊢
    rw [ih]

theorem compactCorner_boundedLipschitz_recipes [Fintype ι] [MetricSpace X] [CompactSpace X]
    (K : Set (Option ι → X)) (hcompact : IsCompact K) (hunique : CornerUnique K)
    (A : Set C(X, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe ι X), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ c ∈ K, |r.value (cornerDelete c) - f (c none)| < ε) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let vertex : ι → C(K, X) := fun j =>
    ⟨fun x => x.val (some j), (continuous_apply (some j)).comp continuous_subtype_val⟩
  let root : C(K, X) := ⟨fun x => x.val none, (continuous_apply none).comp continuous_subtype_val⟩
  obtain ⟨recipes, C, hC, hb, ha⟩ := cornerRecipe_boundedLipschitz_family vertex
    (cornerDelete_injective_on_cubes K hunique) root A B L hB hL ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro c hc
  have hp := happrox ⟨c, hc⟩
  rw [cornerRecipe_eval_eq_value] at hp
  exact hp

end Hindman168
