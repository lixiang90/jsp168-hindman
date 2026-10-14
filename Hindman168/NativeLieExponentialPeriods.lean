import Hindman168.NativeLieExponentialCommutingAdd

/-! The original exponential periods form a genuine closed discrete
additive subgroup of the original model. Equal original exponential
values are exactly vectors differing by one of these actual periods.
This gives the original fibers as actual affine period cosets; it does
not eliminate periods or establish global surjectivity. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_period_add {p : E}
    (hp : nativeLieExponential (I := I) (G := G) p = 1) (v : E) :
    nativeLieExponential (I := I) (G := G) (p + v) =
      nativeLieExponential (I := I) (G := G) v := by
  have h : nativeLieAdjointGenerator (I := I) (G := G) p v = 0 := by
    rw [nativeLieAdjointGenerator_eq_zero_of_exponential_eq_one hp]
    rfl
  rw [nativeLieExponential_add_of_generator_apply_eq_zero h, hp, one_mul]

noncomputable def nativeLieExponentialPeriods : AddSubgroup E where
  carrier := {p : E | nativeLieExponential (I := I) (G := G) p = 1}
  zero_mem' := nativeLieExponential_zero
  add_mem' {p q} hp hq := (nativeLieExponential_period_add hp q).trans hq
  neg_mem' {p} hp := by
    let exp : E → G := nativeLieExponential (I := I) (G := G)
    change exp (-p) = 1
    have hn : exp (-p) = (exp p)⁻¹ := nativeLieExponential_neg (I := I) p
    have hp' : exp p = 1 := hp
    rw [hn, hp', inv_one]

 theorem mem_nativeLieExponentialPeriods (p : E) :
    p ∈ nativeLieExponentialPeriods (I := I) (G := G) ↔
      nativeLieExponential (I := I) (G := G) p = 1 := Iff.rfl

 theorem nativeLieExponential_eq_iff_sub_mem_periods (v w : E) :
    nativeLieExponential (I := I) (G := G) v = nativeLieExponential (I := I) (G := G) w ↔
      v - w ∈ nativeLieExponentialPeriods (I := I) (G := G) := by
  constructor
  · intro h
    have hc : nativeLieAdjointGenerator (I := I) (G := G) v (-w) = 0 := by
      rw [map_neg, nativeLieAdjointGenerator_eq_of_exponential_eq h,
        nativeLieAdjointGenerator_self, neg_zero]
    change nativeLieExponential (I := I) (G := G) (v - w) = 1
    rw [sub_eq_add_neg, nativeLieExponential_add_of_generator_apply_eq_zero hc]
    let exp : E → G := nativeLieExponential (I := I) (G := G)
    change exp v * exp (-w) = 1
    have hn : exp (-w) = (exp w)⁻¹ := nativeLieExponential_neg (I := I) w
    have he : exp v = exp w := h
    rw [hn, he, mul_inv_cancel]
  · intro h
    have hp : nativeLieExponential (I := I) (G := G) (v - w) = 1 := h
    have he := nativeLieExponential_period_add hp w
    simpa only [sub_add_cancel] using he

 theorem nativeLieExponential_fiber_eq_period_translate (w : E) :
    {v : E | nativeLieExponential (I := I) (G := G) v =
      nativeLieExponential (I := I) (G := G) w} =
        (fun p : E => p + w) '' (nativeLieExponentialPeriods (I := I) (G := G) : Set E) := by
  ext v
  constructor
  · intro h
    exact ⟨v - w, (nativeLieExponential_eq_iff_sub_mem_periods v w).mp h, sub_add_cancel v w⟩
  · rintro ⟨p, hp, rfl⟩
    exact nativeLieExponential_period_add hp w

 theorem nativeLieExponentialPeriods_closed :
    IsClosed (nativeLieExponentialPeriods (I := I) (G := G) : Set E) :=
  nativeLieExponential_fiber_closed (I := I) (G := G) 1

 theorem nativeLieExponentialPeriods_discrete :
    IsDiscrete (nativeLieExponentialPeriods (I := I) (G := G) : Set E) :=
  nativeLieExponential_fiber_discrete (I := I) (G := G) 1

 theorem nativeLieExponential_period_translates_disjoint_nhds (v : E) :
    ∃ U : Set E, U ∈ 𝓝 v ∧ ∀ p : E, p ∈ nativeLieExponentialPeriods (I := I) (G := G) →
      (((fun z : E => p + z) '' U) ∩ U).Nonempty → p = 0 := by
  obtain ⟨U, hU, hi⟩ := nativeLieExponential_injOn_nhds (I := I) (G := G) v
  refine ⟨U, hU, ?_⟩
  intro p hp hx
  obtain ⟨x, ⟨z, hz, rfl⟩, hpx⟩ := hx
  have he : p + z = z := hi hpx hz (nativeLieExponential_period_add hp z)
  exact add_right_cancel (he.trans (zero_add z).symm)

end Hindman168
