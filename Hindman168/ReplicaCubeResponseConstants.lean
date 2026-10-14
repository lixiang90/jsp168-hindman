import Hindman168.ReplicaCubeEvaluations

/-!
# Fixed integer factors in the prediction replica direction responses

The response of a row to direction (q,S) is c(q,S,row) M_q. Only the
selected row has c=0. All other fixed integer factors survive modulo
every prime above a single template-dependent threshold. Thus copied
rows need the existing polynomial tests for M_q, with no modulus differences.
-/

namespace Hindman168

open Filter
open scoped BigOperators Classical

def replicaCubeResponseConstant {b d : ℕ} (q : Fin b) (S : CubeVertex d)
    (r : ReplicaCubeRow b d) : ℤ :=
  match r with
  | none => cubeRootDirection S.val
  | some (q', T) => if q' = q then cubeDirectionResponse S.val T.val else cubeRootDirection S.val

theorem replicaCubeResponseConstant_selected {b d : ℕ} (q : Fin b) (S : CubeVertex d) :
    replicaCubeResponseConstant q S (some (q, S)) = 0 := by
  simp only [replicaCubeResponseConstant, ite_true, cubeDirectionResponse_self]

theorem replicaCubeResponseConstant_ne_zero {b d : ℕ} (q : Fin b) (S : CubeVertex d)
    (r : ReplicaCubeRow b d) (hr : r ≠ some (q, S)) :
    replicaCubeResponseConstant q S r ≠ 0 := by
  cases r with
  | none => exact cubeRootDirection_ne_zero S.property
  | some r =>
    rcases r with ⟨q', T⟩
    by_cases hq : q' = q
    · subst q'
      simp only [replicaCubeResponseConstant, ite_true]
      exact cubeDirectionResponse_ne_zero (fun h =>
        hr (congrArg (fun T => some (q, T)) (Subtype.ext h.symm)))
    · simpa only [replicaCubeResponseConstant, if_neg hq] using cubeRootDirection_ne_zero S.property

theorem replicaCubeResponseConstant_zero_iff {b d : ℕ} (q : Fin b) (S : CubeVertex d)
    (r : ReplicaCubeRow b d) : replicaCubeResponseConstant q S r = 0 ↔ r = some (q, S) := by
  constructor
  · intro hz
    by_contra hr
    exact replicaCubeResponseConstant_ne_zero q S r hr hz
  · rintro rfl
    exact replicaCubeResponseConstant_selected q S

theorem replicaCubeDirection_response_factor {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) (r : ReplicaCubeRow b d) :
    replicaCubeEval M r (replicaCubeDirection M q S) = replicaCubeResponseConstant q S r * M q := by
  cases r with
  | none => exact replicaCubeDirection_root_response M q S
  | some r =>
    rcases r with ⟨q', T⟩
    by_cases hq : q' = q
    · subst q'
      rw [replicaCubeDirection_same_response]
      simp only [replicaCubeResponseConstant, ite_true, mul_comm]
    · rw [replicaCubeDirection_other_response M q q' S T hq]
      simp only [replicaCubeResponseConstant, if_neg hq]

noncomputable def replicaCubeResponseBound {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : ℕ :=
  1 + ∑ i, ∑ r : ReplicaCubeRow b d, (replicaCubeResponseConstant (dir i).1 (dir i).2 r).natAbs

theorem replicaCubeResponseConstant_natAbs_le {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (i : Fin h) (r : ReplicaCubeRow b d) :
    (replicaCubeResponseConstant (dir i).1 (dir i).2 r).natAbs ≤ replicaCubeResponseBound dir := by
  unfold replicaCubeResponseBound
  calc
    _ ≤ ∑ t : ReplicaCubeRow b d, (replicaCubeResponseConstant (dir i).1 (dir i).2 t).natAbs :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    _ ≤ ∑ j, ∑ t : ReplicaCubeRow b d, (replicaCubeResponseConstant (dir j).1 (dir j).2 t).natAbs :=
      Finset.single_le_sum
        (f := fun j => ∑ t : ReplicaCubeRow b d, (replicaCubeResponseConstant (dir j).1 (dir j).2 t).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ _ := Nat.le_add_left _ _

theorem integer_mod_nonzero_of_natAbs_lt {p : ℕ} (a : ℤ) (ha : a ≠ 0)
    (hcap : a.natAbs < p) : (a : ZMod p) ≠ 0 := by
  intro hz
  have hd : (p : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz
  have hd' : p ∣ a.natAbs := Int.natCast_dvd.mp hd
  exact (not_le_of_gt hcap) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hd')

theorem replicaCubeResponseConstant_mod_nonzero {b d h w p : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (hbound : replicaCubeResponseBound dir ≤ w)
    (hp : w < p) (i : Fin h) (r : ReplicaCubeRow b d) (hr : r ≠ some (dir i)) :
    (replicaCubeResponseConstant (dir i).1 (dir i).2 r : ZMod p) ≠ 0 :=
  integer_mod_nonzero_of_natAbs_lt _
    (replicaCubeResponseConstant_ne_zero (dir i).1 (dir i).2 r hr)
    (lt_of_le_of_lt ((replicaCubeResponseConstant_natAbs_le dir i r).trans hbound) hp)

theorem replicaCubeResponseConstant_eventually_mod_nonzero {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) :
    ∀ᶠ w in atTop, ∀ p, w < p → ∀ i r, r ≠ some (dir i) →
      (replicaCubeResponseConstant (dir i).1 (dir i).2 r : ZMod p) ≠ 0 :=
  (eventually_ge_atTop (replicaCubeResponseBound dir)).mono (fun _ hw _ hp i r hr =>
    replicaCubeResponseConstant_mod_nonzero dir hw hp i r hr)

end Hindman168
