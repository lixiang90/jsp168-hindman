import Hindman168.RoughParametricPicard
import Hindman168.RoughVectorWeightedDegree

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RoughParametricWeightedDegree (F : ℕ → Submodule ℝ E)
    (p : RoughParametricCurve σ E) (k : ℕ) : Prop :=
  ∀ a ∈ p, RoughVectorMvWeightedDegree F a.2 k

theorem rough_vector_weighted_mono (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hp : RoughVectorMvWeightedDegree F p l) (hkl : k ≤ l) :
    RoughVectorMvWeightedDegree F p k :=
  fun a ha => hF (Nat.add_le_add_left hkl a.1.totalDegree) (hp a ha)

theorem rough_parametric_weighted_mono (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughParametricCurve σ E} {k l : ℕ}
    (hp : RoughParametricWeightedDegree F p l) (hkl : k ≤ l) :
    RoughParametricWeightedDegree F p k :=
  fun a ha => rough_vector_weighted_mono F hF (hp a ha) hkl

theorem rough_parametric_weighted_singleton (F : ℕ → Submodule ℝ E)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) (n : ℕ) :
    RoughParametricWeightedDegree F [(n,p)] k := by
  intro a ha
  exact List.mem_singleton.mp ha ▸ hp

theorem rough_parametric_weighted_append (F : ℕ → Submodule ℝ E)
    {p q : RoughParametricCurve σ E} {k : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q k) :
    RoughParametricWeightedDegree F (p++q) k :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem rough_parametric_weighted_sum (F : ℕ → Submodule ℝ E) (n k : ℕ)
    (p : ℕ → RoughParametricCurve σ E) (hp : ∀ j < n, RoughParametricWeightedDegree F (p j) k) :
    RoughParametricWeightedDegree F (roughParametricSum n p) k := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  exact hp j (List.mem_range.mp hj) a ha

theorem rough_parametric_weighted_endpoint (F : ℕ → Submodule ℝ E)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : RoughParametricWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughParametricEndpoint p) k := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  exact hp b hb a ha

theorem rough_parametric_weighted_scale (F : ℕ → Submodule ℝ E) (r : ℚ)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : RoughParametricWeightedDegree F p k) :
    RoughParametricWeightedDegree F (roughParametricScale r p) k := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact rough_vector_weighted_scale F _ (hp b hb)

theorem rough_parametric_weighted_primitive (F : ℕ → Submodule ℝ E)
    {p : RoughParametricCurve σ E} {k : ℕ} (hp : RoughParametricWeightedDegree F p k) :
    RoughParametricWeightedDegree F (roughParametricPrimitive p) k := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact rough_vector_weighted_scale F _ (hp b hb)

theorem rough_parametric_weighted_bilinear (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p q : RoughParametricCurve σ E} {k l : ℕ}
    (hp : RoughParametricWeightedDegree F p k) (hq : RoughParametricWeightedDegree F q l) :
    RoughParametricWeightedDegree F (roughParametricBilinear B p q) (k+l) := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact rough_vector_weighted_bilinear F hF B hB (hp b hb) (hq c hc)

end Hindman168
