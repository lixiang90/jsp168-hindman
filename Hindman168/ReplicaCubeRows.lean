import Hindman168.PredictionCubeDirections
import Hindman168.MasterMixedWeightedMeanOne

/-!
# Actual integer prediction cube rows in independent replicas

There is one root variable and separate pairs of shift variables for
each replica. A nonroot row is y + M_q sum_{j in S}(u_{q,j}^1-u_{q,j}^0).
Every row has anchor coefficient one. Any two distinct rows have a
distinguishing shift coefficient equal to one replica modulus (up to
sign); no difference of two replica moduli is needed.
-/

namespace Hindman168

open scoped BigOperators Classical

abbrev CubeVertex (d : ℕ) := {S : Finset (Fin d) // S.Nonempty}
abbrev ReplicaCubeRow (b d : ℕ) := Option (Fin b × CubeVertex d)
abbrev ReplicaCubeColumn (b d : ℕ) := Option (Fin b × Fin d × Bool)

noncomputable def replicaCubeCoefficient {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (r : ReplicaCubeRow b d) (col : ReplicaCubeColumn b d) : R :=
  match col with
  | none => 1
  | some (q, j, bit) => match r with
    | none => 0
    | some (q', S) => if q = q' ∧ j ∈ S.val then (if bit then M q' else -(M q')) else 0

theorem replicaCubeCoefficient_anchor {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (r : ReplicaCubeRow b d) : replicaCubeCoefficient M r none = 1 := rfl

theorem replicaCubeCoefficient_map {R T : Type*} [CommRing R] [CommRing T] {b d : ℕ}
    (f : R →+* T) (M : Fin b → R) (r : ReplicaCubeRow b d) (col : ReplicaCubeColumn b d) :
    f (replicaCubeCoefficient M r col) = replicaCubeCoefficient (fun q => f (M q)) r col := by
  cases col with
  | none => exact map_one f
  | some col =>
    rcases col with ⟨q, j, bit⟩
    cases r with
    | none => exact map_zero f
    | some r =>
      rcases r with ⟨q', S⟩
      simp only [replicaCubeCoefficient]
      split_ifs <;> simp only [map_zero, map_neg]

theorem replicaCubeCoefficient_intCast {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → ℤ) (r : ReplicaCubeRow b d) (col : ReplicaCubeColumn b d) :
    ((replicaCubeCoefficient M r col : ℤ) : R) = replicaCubeCoefficient (fun q => (M q : R)) r col := by
  cases col with
  | none => exact Int.cast_one
  | some col =>
    rcases col with ⟨q, j, bit⟩
    cases r with
    | none => exact Int.cast_zero
    | some r =>
      rcases r with ⟨q', S⟩
      simp only [replicaCubeCoefficient]
      split_ifs <;> simp only [Int.cast_zero, Int.cast_neg]

theorem replicaCubeCoefficient_distinguishing {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (hM : ∀ q, M q ≠ 0) (r s : ReplicaCubeRow b d) (hrs : r ≠ s) :
    ∃ col, replicaCubeCoefficient M r col ≠ replicaCubeCoefficient M s col := by
  cases r with
  | none =>
    cases s with
    | none => exact False.elim (hrs rfl)
    | some s =>
      rcases s with ⟨q, S⟩
      obtain ⟨j, hj⟩ := S.property
      exact ⟨some (q, j, true), by simpa [replicaCubeCoefficient, hj] using (hM q).symm⟩
  | some r =>
    rcases r with ⟨q, S⟩
    cases s with
    | none =>
      obtain ⟨j, hj⟩ := S.property
      exact ⟨some (q, j, true), by simpa [replicaCubeCoefficient, hj] using hM q⟩
    | some s =>
      rcases s with ⟨q', T⟩
      by_cases hq : q = q'
      · subst q'
        have hST : S.val ≠ T.val := by
          intro h
          exact hrs (congrArg (fun S => some (q, S)) (Subtype.ext h))
        have hex : ∃ j, ¬ (j ∈ S.val ↔ j ∈ T.val) := by
          by_contra! h
          exact hST (Finset.ext h)
        obtain ⟨j, hj⟩ := hex
        refine ⟨some (q, j, true), ?_⟩
        simp only [replicaCubeCoefficient, true_and, ite_true]
        by_cases hS : j ∈ S.val <;> by_cases hT : j ∈ T.val
        · exact False.elim (hj (by simp only [hS, hT]))
        · simpa only [if_pos hS, if_neg hT] using hM q
        · simpa only [if_neg hS, if_pos hT] using (hM q).symm
        · exact False.elim (hj (by simp only [hS, hT]))
      · obtain ⟨j, hj⟩ := S.property
        exact ⟨some (q, j, true), by simpa [replicaCubeCoefficient, hq, hj] using hM q⟩

theorem anchored_rows_pair_independent {R I : Type*} [CommRing R] [IsDomain R]
    (c e : I → R) (root : I) (hc : c root = 1) (he : e root = 1)
    (hd : ∃ j, c j ≠ e j) : LinearIndependent R ![c, e] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have hroot : s + t = 0 := by simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc, he,
    mul_one, Pi.zero_apply] using congrFun h root
  have hs : s = -t := eq_neg_of_add_eq_zero_left hroot
  obtain ⟨j, hj⟩ := hd
  have hj0 : s * c j + t * e j = 0 := congrFun h j
  have hm : t * (e j - c j) = 0 := by
    calc
      _ = s * c j + t * e j := by rw [hs]; ring
      _ = 0 := hj0
  have ht : t = 0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hj.symm)
  exact ⟨by simpa only [ht, neg_zero] using hs, ht⟩

theorem replicaCubeCoefficient_pair_independent {R : Type*} [CommRing R] [IsDomain R] {b d : ℕ}
    (M : Fin b → R) (hM : ∀ q, M q ≠ 0) (r s : ReplicaCubeRow b d) (hrs : r ≠ s) :
    LinearIndependent R ![replicaCubeCoefficient M r, replicaCubeCoefficient M s] :=
  anchored_rows_pair_independent _ _ none rfl rfl (replicaCubeCoefficient_distinguishing M hM r s hrs)

noncomputable def replicaCubeFinCoefficient {b d : ℕ} (M : Fin b → ℤ)
    (r : ReplicaCubeRow b d) (j : Fin (Fintype.card (ReplicaCubeColumn b d))) : ℤ :=
  replicaCubeCoefficient M r ((Fintype.equivFin (ReplicaCubeColumn b d)).symm j)

theorem replicaCubeFinCoefficient_primitive {p b d : ℕ} (hp : p.Prime)
    (M : Fin b → ℤ) (r : ReplicaCubeRow b d) :
    ∃ j, (replicaCubeFinCoefficient M r j : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨Fintype.equivFin (ReplicaCubeColumn b d) none, ?_⟩
  simp only [replicaCubeFinCoefficient, Equiv.symm_apply_apply, replicaCubeCoefficient_anchor,
    Int.cast_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem replicaCubeFinCoefficient_pair_independent {p b d : ℕ} (hp : p.Prime)
    (M : Fin b → ℤ) (hM : ∀ q, (M q : ZMod p) ≠ 0)
    (r s : ReplicaCubeRow b d) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (replicaCubeFinCoefficient M r j : ZMod p)),
        (fun j => (replicaCubeFinCoefficient M s j : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  let root := Fintype.equivFin (ReplicaCubeColumn b d) none
  apply anchored_rows_pair_independent _ _ root
  · simp only [root, replicaCubeFinCoefficient, Equiv.symm_apply_apply,
      replicaCubeCoefficient_anchor, Int.cast_one]
  · simp only [root, replicaCubeFinCoefficient, Equiv.symm_apply_apply,
      replicaCubeCoefficient_anchor, Int.cast_one]
  · obtain ⟨col, hcol⟩ := replicaCubeCoefficient_distinguishing
      (fun q => (M q : ZMod p)) hM r s hrs
    refine ⟨Fintype.equivFin (ReplicaCubeColumn b d) col, ?_⟩
    simpa only [replicaCubeFinCoefficient, Equiv.symm_apply_apply, replicaCubeCoefficient_intCast] using hcol

end Hindman168
