import Hindman168.PolynomialRowDirectionCatalog
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Symbolic prime branches preserve nonzero row minors

Three column tags mean unaffected, the first selected column and the second
selected column. The two branches multiply them by (1,p,q) and (1,q,p).
For a one-coordinate insertion only one nonzero tag is used. Invariant rows
are kept without a new multiplier. Recovering at p=q=1 treats descendants
of distinct old rows; a separate polynomial determinant treats two copies
of one noninvariant row. No numerical prime tuple is selected here.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def freshMaskMultiplier {R : Type*} [CommRing R]
    (branch : Bool) (tag : Fin 3) : MvPolynomial Bool R :=
  if tag = 0 then 1 else if tag = 1 then MvPolynomial.X branch else MvPolynomial.X (!branch)

noncomputable def maskBranchRow {R : Type*} [CommRing R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (branch : Option Bool) :
    Fin c → MvPolynomial Bool R :=
  fun k => MvPolynomial.C (A k) * branch.elim 1 (fun b => freshMaskMultiplier b (tag k))

theorem freshMaskMultiplier_recover {R : Type*} [CommRing R] (b : Bool) (t : Fin 3) :
    MvPolynomial.eval (fun _ => (1 : R)) (freshMaskMultiplier b t) = 1 := by
  unfold freshMaskMultiplier
  split_ifs <;> simp

theorem maskBranchRow_recover {R : Type*} [CommRing R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (b : Option Bool) (k : Fin c) :
    MvPolynomial.eval (fun _ => (1 : R)) (maskBranchRow A tag b k) = A k := by
  cases b <;> simp [maskBranchRow, freshMaskMultiplier_recover]

theorem maskBranchRow_ne_zero_iff {R : Type*} [CommRing R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (b : Option Bool) (k : Fin c) :
    maskBranchRow A tag b k ≠ 0 ↔ A k ≠ 0 := by
  constructor
  · intro hn hz
    exact hn (by simp [maskBranchRow, hz])
  · intro hn hz
    have h := congrArg (MvPolynomial.eval (fun _ => (1 : R))) hz
    rw [maskBranchRow_recover, map_zero] at h
    exact hn h

theorem maskBranchRow_minor_recover {R : Type*} [CommRing R] {c : ℕ}
    (A B : Fin c → R) (tag : Fin c → Fin 3) (a b : Option Bool) (j k : Fin c) :
    MvPolynomial.eval (fun _ => (1 : R))
      (polynomialRowMinor (maskBranchRow A tag a) (maskBranchRow B tag b) j k) =
      polynomialRowMinor A B j k := by
  simp [polynomialRowMinor, maskBranchRow_recover]

theorem maskBranchRow_old_minor_nonzero {R : Type*} [CommRing R] {c : ℕ}
    (A B : Fin c → R) (tag : Fin c → Fin 3) (a b : Option Bool) (j k : Fin c)
    (h : polynomialRowMinor A B j k ≠ 0) :
    polynomialRowMinor (maskBranchRow A tag a) (maskBranchRow B tag b) j k ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval (fun _ => (1 : R))) hz
  rw [maskBranchRow_minor_recover, map_zero] at he
  exact h he

theorem freshMaskMultiplier_cross_nonzero {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] (a b : Bool) (hab : a ≠ b)
    (s t : Fin 3) (hst : s ≠ t) :
    freshMaskMultiplier (R := R) a s * freshMaskMultiplier b t -
      freshMaskMultiplier a t * freshMaskMultiplier b s ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval (fun b => if b then (3 : R) else 2)) hz
  cases a <;> cases b
  all_goals try contradiction
  all_goals fin_cases s
  all_goals fin_cases t
  all_goals norm_num [freshMaskMultiplier] at *

theorem maskBranchRow_same_minor_nonzero {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {c : ℕ}
    (A : Fin c → R) (tag : Fin c → Fin 3) (a b : Bool) (hab : a ≠ b)
    (j k : Fin c) (hj : A j ≠ 0) (hk : A k ≠ 0) (ht : tag j ≠ tag k) :
    polynomialRowMinor (maskBranchRow A tag (some a)) (maskBranchRow A tag (some b)) j k ≠ 0 := by
  have hc : (MvPolynomial.C (A j * A k) : MvPolynomial Bool R) ≠ 0 := by
    intro hz
    apply mul_ne_zero hj hk
    exact MvPolynomial.C_injective Bool R (by simpa only [map_zero] using hz)
  have hid : polynomialRowMinor (maskBranchRow A tag (some a)) (maskBranchRow A tag (some b)) j k =
      MvPolynomial.C (A j * A k) *
        (freshMaskMultiplier a (tag j) * freshMaskMultiplier b (tag k) -
          freshMaskMultiplier a (tag k) * freshMaskMultiplier b (tag j)) := by
    simp only [polynomialRowMinor, maskBranchRow, Option.elim_some, map_mul]
    ring
  rw [hid]
  exact mul_ne_zero hc (freshMaskMultiplier_cross_nonzero a b hab _ _ ht)

end Hindman168
