import Hindman168.NativeLieRationalInternalGeneration

/-! A stable rational subspace absorbs the next-layer remainder in a
terminating actual internal lower-central series. The induction lowers
the genuine remaining layer to zero; it does not discard that layer. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieRationalInternalLayer_step_descent
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (N : Submodule ℚ E)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, nativeLieAdjointDifferential (I := I) (G := G) v n ∈ N)
    (j : ℕ)
    (hstep : nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤
      N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1)) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) ≤
      N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2) := by
  apply (nativeLieRationalInternalLayer_succ_le_iff V hbr j _).mpr
  intro v hv w hw
  let A : E →ₗ[ℚ] E := (nativeLieAdjointDifferential (I := I) (G := G) v).toLinearMap.restrictScalars ℚ
  have hn : N ≤ (N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2)).comap A :=
    fun _ hx => Submodule.mem_sup_left (hideal v hv _ hx)
  have hf : nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) ≤
      (N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2)).comap A :=
    fun _ hx => Submodule.mem_sup_right (nativeLieRationalInternalLayer_differential_next V hbr (j + 1) hv hx)
  exact (sup_le hn hf) (hstep hw)

 theorem nativeLieRationalInternalLayer_absorb_next [Group.IsNilpotent G]
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (N : Submodule ℚ E)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, nativeLieAdjointDifferential (I := I) (G := G) v n ∈ N)
    (j : ℕ)
    (hstep : nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤
      N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1)) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤ N := by
  have hshift : ∀ n : ℕ, nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + n) ≤
      N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.add_zero] using hstep
    | succ n ih =>
      exact nativeLieRationalInternalLayer_step_descent V hbr N hideal (j + n) ih
  have hremain : ∀ n : ℕ, nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤
      N ⊔ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + n) := by
    intro n
    induction n with
    | zero => exact le_sup_right
    | succ n ih => exact ih.trans (sup_le le_sup_left (hshift n))
  have hb : nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + Group.nilpotencyClass G) = ⊥ := by
    apply le_antisymm _ bot_le
    have hl := nativeLieRationalInternalLayer_antitone (I := I) (G := G) V hbr
      (show Group.nilpotencyClass G ≤ j + Group.nilpotencyClass G by omega)
    rw [nativeLieRationalInternalLayer_nilpotencyClass_bot] at hl
    exact hl
  have h := hremain (Group.nilpotencyClass G)
  rw [hb, sup_bot_eq] at h
  exact h

end Hindman168
