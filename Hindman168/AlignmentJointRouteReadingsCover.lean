import Hindman168.AlignmentJointRouteReadings
import Hindman168.PositivePrincipalSumMassThresholds

/-! The closed comparison sets contain only quotient readings and finite
route arithmetic. In particular their definitions contain no chosen coset,
coordinate projection, or native shear lift. The proved nilpotent recurrence
supplies the pointwise cover after the genuine terminal-word identification. -/
namespace Hindman168
open scoped Classical
universe u v

/-- The closed option F_o of the original quotient. Its center uses R_(v,0)
and its terminal uses R_(v+m,m), with v and m computed without the lifts. -/
def alignmentJointRouteClosedSet {n : ℕ} {i : Fin n} {Y κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → Y → ℝ)
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) : Set Y :=
  let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
  {y | ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
    read (insert i request.tail) (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail))
        c arithmetic.2.toAdd 0 y ≤ 3*θ/2 ∨
    3*θ/2 ≤ read (insert i request.tail)
        (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c
        (arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word)
        (alignmentAuxiliaryWord q₀ arithmetic.1 word) y}

theorem alignment_joint_route_closed {n : ℕ} {i : Fin n} {Y κ : Type*}
    [TopologicalSpace Y]
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → Y → ℝ)
    (hread : ∀ B a c stored query, Continuous (read B a c stored query))
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) :
    IsClosed (alignmentJointRouteClosedSet read θ q₀ plan b requests route) := by
  unfold alignmentJointRouteClosedSet
  simp only [Set.setOf_forall, Set.setOf_or]
  repeat (apply isClosed_iInter; intro)
  exact (isClosed_le (hread _ _ _ _ _) continuous_const).union
    (isClosed_le continuous_const (hread _ _ _ _ _))

/-- Turn a successful actual recurrence route into membership in the fixed
quotient comparison set. Only own-letter equivariance for each FINAL stored
factor is used; the cumulative route can involve arbitrary other targets. -/
theorem alignment_joint_successful_route_closed
    {σ Y κ : Type*} {n : ℕ} {i : Fin n} (w : σ → ℕ)
    (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
    (projection : (σ → ℝ) → Y)
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → Y → ℝ)
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (z : σ → ℝ)
    (hreq : ∀ request ∈ requests,
      alignmentPivotRequestHolds q₀
        (principalPivotRouteValue q₀ (alignmentJointShearLetter w L) plan b route).1
        (alignmentJointShearLetter w L)
        (fun B a x c => decide (3*θ/2 < read B a c x.2.toAdd 0 (projection x.1)))
        ((principalPivotRouteValue q₀ (alignmentJointShearLetter w L) plan b route).2 •
          (z, Multiplicative.ofAdd 0)) request)
    (hstep : ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
      let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
      let B := insert i request.tail
      let lead := a * finiteScaleBlockProduct arithmetic.1 B
      let stored := arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word
      ∀ l ∈ word, ∀ query x,
        read B lead c stored query (projection (L l.1 • x)) =
          read B lead c stored (query + alignmentAuxiliaryUnit l.1 1) (projection x)) :
    projection ((principalPivotRouteValue q₀ L plan b route).2 • z) ∈
      alignmentJointRouteClosedSet read θ q₀ plan b requests route := by
  let joint := principalPivotRouteValue q₀ (alignmentJointShearLetter w L) plan b route
  let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
  let y : AlignmentJointShearState (σ := σ) (i := i) := joint.2 • (z, Multiplicative.ofAdd 0)
  have harith := alignment_joint_route_arithmetic w L q₀ plan b route
  have hscale : joint.1 = arithmetic.1 := (congrArg Prod.fst harith).symm
  have hslot : y.2.toAdd = arithmetic.2.toAdd := by
    change (joint.2.2 * Multiplicative.ofAdd 0).toAdd = _
    rw [show Multiplicative.ofAdd (0 : AlignmentAddingPair n i → ℤ) = 1 from rfl, mul_one]
    exact congrArg Multiplicative.toAdd (congrArg Prod.snd harith).symm
  have hfirst : y.1 = (principalPivotRouteValue q₀ L plan b route).2 • z := by
    have hh := alignment_pivot_route_map (MonoidHom.fst _ _) q₀
      (alignmentJointShearLetter w L) plan b route
    exact congrArg (fun g => g • z) (congrArg Prod.snd hh).symm
  change ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c, _
  intro request hr a ha word hw c
  have he := congrFun (hreq request hr a ha word hw) c
  change decide (3*θ/2 < read _ _ c y.2.toAdd 0 (projection y.1)) =
    decide (3*θ/2 < read _ _ c
      (alignmentWordValue q₀ joint.1 (alignmentJointShearLetter w L) word • y).2.toAdd 0
      (projection (alignmentWordValue q₀ joint.1 (alignmentJointShearLetter w L) word • y).1)) at he
  rw [hscale] at he
  have hterminal := alignment_joint_terminal_word_reading w L projection
    (read (insert i request.tail) (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c)
    q₀ arithmetic.1 word y (by simpa only [hslot] using hstep request hr a ha word hw c)
  rw [hterminal, hslot, hfirst] at he
  by_cases hc : 3*θ/2 < read (insert i request.tail)
      (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c
      arithmetic.2.toAdd 0 (projection ((principalPivotRouteValue q₀ L plan b route).2 • z))
  · right
    have ht := he.symm.trans (show decide (3*θ/2 < read (insert i request.tail)
      (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c
      arithmetic.2.toAdd 0 (projection ((principalPivotRouteValue q₀ L plan b route).2 • z))) = true by
        simpa using hc)
    exact (of_decide_eq_true ht).le
  · exact Or.inl (le_of_not_gt hc)

/-- A genuine finite recurrence plan yields the pointwise closed cover.
Plan and q₀ precede the coordinate dimension, lifts, projection and readings.
The only model input is the proved single-letter equivariance at the finite
terminal factors; no pointwise cover or successful route is assumed. -/
theorem alignment_joint_recurrence_closed_cover {n : ℕ} {i : Fin n}
    {κ : Type} [Finite κ] (s : ℕ) (hs : 1 ≤ s)
    (requests : List (AlignmentPivotRequest n i)) :
    ∃ plan : List (AlignmentPivotStage n i), ∀ incoming : Finset (Fin n → ℚ),
      ∃ q₀ : ℕ, 0 < q₀ ∧
      ∀ (σ : Type u) (Y : Type v) (w : σ → ℕ) (hw : ∀ j, w j ≤ s)
        (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
        (projection : (σ → ℝ) → Y)
        (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
          (AlignmentAddingPair n i → ℤ) → Y → ℝ)
        (θ : ℝ) (b : Fin n → ℚ) (_hb : b ∈ incoming) (_hpos : ∀ j, 0 < b j),
      (∀ route ∈ principalPivotRoutes plan,
        ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
        let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
        let B := insert i request.tail
        let lead := a * finiteScaleBlockProduct arithmetic.1 B
        let stored := arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word
        ∀ l ∈ word, ∀ query x,
          read B lead c stored query (projection (L l.1 • x)) =
            read B lead c stored (query + alignmentAuxiliaryUnit l.1 1) (projection x)) →
      ∀ z : σ → ℝ, ∃ route ∈ principalPivotRoutes plan,
        projection ((principalPivotRouteValue q₀ L plan b route).2 • z) ∈
          alignmentJointRouteClosedSet read θ q₀ plan b requests route := by
  obtain ⟨plan, hp⟩ := principal_recurrence_finite_routes.{u,u}
    (Color := κ → Bool) s requests
  refine ⟨plan, ?_⟩
  intro incoming
  obtain ⟨q₀, hq, hplan⟩ := hp incoming
  refine ⟨q₀, hq, ?_⟩
  intro σ Y w hw L projection read θ b hb hpos hstep z
  obtain ⟨route, hr, hreq⟩ := hplan (AlignmentJointShearGroup (i := i) w)
    (AlignmentJointShearState (σ := σ) (i := i)) (alignmentJointShearLetter w L)
    (alignment_joint_shear_group_step w s hw hs)
    (fun B a x c => decide (3*θ/2 < read B a c x.2.toAdd 0 (projection x.1)))
    b hb hpos (z, Multiplicative.ofAdd 0)
  exact ⟨route, hr, alignment_joint_successful_route_closed w L projection read θ q₀
    plan b requests route z hreq (hstep route hr)⟩

end Hindman168
