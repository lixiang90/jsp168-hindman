import Hindman168.AdditiveRowCopiedCoefficients

/-! Modular certificates for actual general copied rows, including all stages. -/

namespace Hindman168

open scoped BigOperators Classical

theorem rows_pair_independent_of_zero_response {R I : Type*} [CommRing R] [IsDomain R]
    [Fintype I] (c e v : I → R) (hc : ∃ j, c j ≠ 0)
    (hz : ∑ j, c j * v j = 0) (he : ∑ j, e j * v j ≠ 0) :
    LinearIndependent R ![c, e] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have hh : s * (∑ j, c j * v j) + t * (∑ j, e j * v j) = 0 := by
    calc
      _ = ∑ j, (s * c j + t * e j) * v j := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := Finset.sum_eq_zero (fun j _ => by
        have hj : s * c j + t * e j = 0 := congrFun h j
        rw [hj, zero_mul])
  rw [hz, mul_zero, zero_add] at hh
  have ht : t = 0 := (mul_eq_zero.mp hh).resolve_right he
  obtain ⟨j, hj⟩ := hc
  have hs : s = 0 := (mul_eq_zero.mp (by
    have hcol : s * c j + t * e j = 0 := congrFun h j
    simpa only [ht, zero_mul, add_zero] using hcol)).resolve_right hj
  exact ⟨hs, ht⟩

theorem rows_pair_independent_of_zero_coordinate {R I : Type*} [CommRing R] [IsDomain R]
    (c e : I → R) (j : I) (hc : c j ≠ 0) (hz : e j = 0) (he : ∃ k, e k ≠ 0) :
    LinearIndependent R ![c, e] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have hcol : s * c j + t * e j = 0 := congrFun h j
  rw [hz, mul_zero, add_zero] at hcol
  have hs : s = 0 := (mul_eq_zero.mp hcol).resolve_right hc
  obtain ⟨k, hk⟩ := he
  have hcol' : s * c k + t * e k = 0 := congrFun h k
  rw [hs, zero_mul, zero_add] at hcol'
  exact ⟨hs, (mul_eq_zero.mp hcol').resolve_right hk⟩

namespace AdditiveRowData

variable {b c : ℕ}

structure ResidueConditions (D : AdditiveRowData b c) (p : ℕ) : Prop where
  primitive : ∀ i, ∃ j, (D.coefficient i j : ZMod p) ≠ 0
  response_unit : ∀ k i, i ≠ some (additiveRowAssigned b k) →
    IsUnit (D.response i k : ZMod p)

theorem response_cast (D : AdditiveRowData b c) (p : ℕ) (i : ReplicaCubeRow b 1) (k : Fin b) :
    (∑ j, (D.coefficient i j : ZMod p) * (D.direction k j : ZMod p)) =
      (D.response i k : ZMod p) := by
  simp only [response, form, Int.cast_sum, Int.cast_mul]

theorem ResidueConditions.base_pair_independent {D : AdditiveRowData b c} {p : ℕ}
    (H : D.ResidueConditions p) (hp : p.Prime) (r s : ReplicaCubeRow b 1) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (D.coefficient r j : ZMod p)), (fun j => (D.coefficient s j : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpair : ∀ k i, some (additiveRowAssigned b k) ≠ i →
      LinearIndependent (ZMod p)
        ![(fun j => (D.coefficient (some (additiveRowAssigned b k)) j : ZMod p)),
          (fun j => (D.coefficient i j : ZMod p))] := by
    intro k i hi
    apply rows_pair_independent_of_zero_response _ _ (fun j => (D.direction k j : ZMod p))
      (H.primitive _)
    · rw [D.response_cast, D.response_own, Int.cast_zero]
    · rw [D.response_cast]
      exact (H.response_unit k i hi.symm).ne_zero
  cases r with
  | some a =>
    obtain ⟨k, rfl⟩ := additiveRowAssigned_surjective b a
    exact hpair k s hrs
  | none =>
    cases s with
    | none => exact False.elim (hrs rfl)
    | some a =>
      obtain ⟨k, rfl⟩ := additiveRowAssigned_surjective b a
      rw [LinearIndependent.pair_symm_iff]
      exact hpair k none hrs.symm

theorem ResidueConditions.copied_primitive {D : AdditiveRowData b c} {p : ℕ}
    (H : D.ResidueConditions p) (r : CopiedReplicaCubeRow (additiveRowAssigned b)) :
    ∃ j, (D.copiedCoefficient r j : ZMod p) ≠ 0 := by
  obtain ⟨j, hj⟩ := H.primitive r.val.1
  exact ⟨.inl j, hj⟩

theorem ResidueConditions.copied_pair_independent {D : AdditiveRowData b c} {p : ℕ}
    (H : D.ResidueConditions p) (hp : p.Prime)
    (r s : CopiedReplicaCubeRow (additiveRowAssigned b)) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (D.copiedCoefficient r j : ZMod p)),
        (fun j => (D.copiedCoefficient s j : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hbase : r.val.1 = s.val.1
  · have hchoices : r.val.2 ≠ s.val.2 := by
      intro he
      exact hrs (Subtype.ext (Prod.ext hbase he))
    have hex : ∃ k, r.val.2 k ≠ s.val.2 k := by
      by_contra! he
      exact hchoices (funext he)
    obtain ⟨k, hk⟩ := hex
    have hactive : r.val.1 ≠ some (additiveRowAssigned b k) := by
      intro he
      exact hk ((r.property k he).trans (s.property k (hbase.symm.trans he)).symm)
    apply rows_pair_independent_of_zero_coordinate _ _ (.inr (k, r.val.2 k))
    · simpa only [copiedCoefficient, ite_true] using (H.response_unit k _ hactive).ne_zero
    · simp only [copiedCoefficient, if_neg hk, Int.cast_zero]
    · exact H.copied_primitive s
  · apply LinearIndependent.pair_iff.mpr
    intro a e h
    apply (LinearIndependent.pair_iff.mp (H.base_pair_independent hp _ _ hbase)) a e
    funext j
    exact congrFun h (.inl j)

theorem ResidueConditions.copiedFin_primitive {D : AdditiveRowData b c} {p : ℕ}
    (H : D.ResidueConditions p) (r : CopiedReplicaCubeRow (additiveRowAssigned b)) :
    ∃ j, (D.copiedFinCoefficient r j : ZMod p) ≠ 0 := by
  obtain ⟨j, hj⟩ := H.copied_primitive r
  refine ⟨Fintype.equivFin (AdditiveCopiedColumn b c) j, ?_⟩
  simpa only [copiedFinCoefficient, Equiv.symm_apply_apply] using hj

theorem ResidueConditions.copiedFin_pair_independent {D : AdditiveRowData b c} {p : ℕ}
    (H : D.ResidueConditions p) (hp : p.Prime)
    (r s : CopiedReplicaCubeRow (additiveRowAssigned b)) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (D.copiedFinCoefficient r j : ZMod p)),
        (fun j => (D.copiedFinCoefficient s j : ZMod p))] := by
  apply LinearIndependent.pair_iff.mpr
  intro a e h
  apply (LinearIndependent.pair_iff.mp (H.copied_pair_independent hp r s hrs)) a e
  funext j
  have hj := congrFun h (Fintype.equivFin (AdditiveCopiedColumn b c) j)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    copiedFinCoefficient, Equiv.symm_apply_apply] using hj

end AdditiveRowData
end Hindman168
