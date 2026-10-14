import Hindman168.RoughParametricCurve

namespace Hindman168

variable {σ E : Type*}

def RoughParametricDegreeLE (p : RoughParametricCurve σ E) (d : ℕ) : Prop :=
  ∀ a ∈ p, RoughVectorMvDegreeLE a.2 d

theorem roughParametricDegreeLE_mono {p : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (h : d ≤ e) : RoughParametricDegreeLE p e :=
  fun a ha => roughVectorMvDegreeLE_mono (hp a ha) h

theorem roughParametricDegreeLE_singleton {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (n : ℕ) : RoughParametricDegreeLE [(n,p)] d := by
  intro a ha
  exact List.mem_singleton.mp ha ▸ hp

theorem roughParametricDegreeLE_append {p q : RoughParametricCurve σ E} {d : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q d) :
    RoughParametricDegreeLE (p ++ q) d :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem roughParametricDegreeLE_sum (n d : ℕ) (p : ℕ → RoughParametricCurve σ E)
    (hp : ∀ j < n, RoughParametricDegreeLE (p j) d) :
    RoughParametricDegreeLE (roughParametricSum n p) d := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  exact hp j (List.mem_range.mp hj) a ha

theorem roughParametricDegreeLE_endpoint {p : RoughParametricCurve σ E} {d : ℕ}
    (hp : RoughParametricDegreeLE p d) : RoughVectorMvDegreeLE (roughParametricEndpoint p) d := by
  intro a ha
  obtain ⟨q, hq, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  exact hp b hb a ha

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem roughParametricDegreeLE_scale (r : ℚ) {p : RoughParametricCurve σ E} {d : ℕ}
    (hp : RoughParametricDegreeLE p d) : RoughParametricDegreeLE (roughParametricScale r p) d := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact roughVectorMvDegreeLE_scale _ (hp b hb)

theorem roughParametricDegreeLE_primitive {p : RoughParametricCurve σ E} {d : ℕ}
    (hp : RoughParametricDegreeLE p d) : RoughParametricDegreeLE (roughParametricPrimitive p) d := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact roughVectorMvDegreeLE_scale _ (hp b hb)

theorem roughParametricDegreeLE_bilinear (B : E →L[ℝ] (E →L[ℝ] E))
    {p q : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q e) :
    RoughParametricDegreeLE (roughParametricBilinear B p q) (d + e) := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact roughVectorMvDegreeLE_bilinear B (hp b hb) (hq c hc)

theorem roughParametricDegreeLE_ad (B : E →L[ℝ] (E →L[ℝ] E))
    {p q : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q e) (n : ℕ) :
    RoughParametricDegreeLE (roughParametricAd B p q n) (n * d + e) := by
  induction n with
  | zero => simpa only [roughParametricAd, zero_mul, zero_add] using hq
  | succ n ih =>
    simpa only [roughParametricAd, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm] using
      roughParametricDegreeLE_bilinear B hp ih

end Hindman168
