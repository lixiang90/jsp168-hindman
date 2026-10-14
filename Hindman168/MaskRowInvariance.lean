import Hindman168.MaskBranchPolynomialRows

/-! The invariant/noninvariant classification has exact minor evidence. -/

namespace Hindman168

open scoped BigOperators Classical

def maskRowInvariant {R : Type*} [Zero R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) : Prop :=
  ∀ j k, A j ≠ 0 → A k ≠ 0 → tag j = tag k

theorem not_maskRowInvariant_iff {R : Type*} [Zero R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) :
    ¬ maskRowInvariant A tag ↔ ∃ j k, A j ≠ 0 ∧ A k ≠ 0 ∧ tag j ≠ tag k := by
  constructor
  · intro h
    unfold maskRowInvariant at h
    push Not at h
    exact h
  · rintro ⟨j, k, hj, hk, ht⟩ hi
    exact ht (hi j k hj hk)

theorem invariant_maskBranchRow_scalar {R : Type*} [CommRing R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (hi : maskRowInvariant A tag)
    (anchor : Fin c) (ha : A anchor ≠ 0) (b : Bool) :
    maskBranchRow A tag (some b) =
      fun k => MvPolynomial.C (A k) * freshMaskMultiplier b (tag anchor) := by
  funext k
  by_cases hk : A k = 0
  · simp [maskBranchRow, hk]
  · simp only [maskBranchRow, Option.elim_some, hi k anchor hk ha]

theorem maskRowInvariant_iff_branch_minors_zero {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) :
    maskRowInvariant A tag ↔ ∀ j k,
      polynomialRowMinor (maskBranchRow A tag (some false))
        (maskBranchRow A tag (some true)) j k = 0 := by
  constructor
  · intro hi j k
    by_cases hj : A j = 0
    · simp [polynomialRowMinor, maskBranchRow, hj]
    by_cases hk : A k = 0
    · simp [polynomialRowMinor, maskBranchRow, hk]
    have ht := hi j k hj hk
    simp only [polynomialRowMinor, maskBranchRow, Option.elim_some, ht]
    ring
  · intro hz j k hj hk
    by_contra ht
    exact maskBranchRow_same_minor_nonzero A tag false true (by decide) j k hj hk ht (hz j k)

theorem noninvariant_maskBranchRow_pair_minor {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (hi : ¬ maskRowInvariant A tag)
    (a b : Bool) (hab : a ≠ b) :
    ∃ j k, polynomialRowMinor (maskBranchRow A tag (some a)) (maskBranchRow A tag (some b)) j k ≠ 0 := by
  obtain ⟨j, k, hj, hk, ht⟩ := (not_maskRowInvariant_iff A tag).mp hi
  exact ⟨j, k, maskBranchRow_same_minor_nonzero A tag a b hab j k hj hk ht⟩

end Hindman168
