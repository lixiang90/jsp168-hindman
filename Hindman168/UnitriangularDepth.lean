import Hindman168.UnitriangularGroup

/-! Actual closed superdiagonal layers of unit upper-triangular matrices.
Depth k means all entries with positive column-row gap less than k vanish.
The subgroup inverse law is proved from the actual matrix inverse equation. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

 def UnitriangularDepth (k : ℕ) (u : Unitriangular n R) : Prop :=
  ∀ i j : Fin n, i < j → j.val < i.val + k →
    (u.val : Matrix (Fin n) (Fin n) R) i j = 0

 theorem unitriangularDepth_one (k : ℕ) : UnitriangularDepth k (1 : Unitriangular n R) := by
  intro i j hij _
  exact Matrix.one_apply_ne (ne_of_lt hij)

 theorem UnitriangularDepth.mul {k : ℕ} {u v : Unitriangular n R}
    (hu : UnitriangularDepth k u) (hv : UnitriangularDepth k v) :
    UnitriangularDepth k (u * v) := by
  classical
  intro i j hij hgap
  change ((u.val : Matrix (Fin n) (Fin n) R) *
    (v.val : Matrix (Fin n) (Fin n) R)) i j = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  rcases lt_trichotomy r i with hr | heq | hr
  · rw [u.property.1 hr, zero_mul]
  · subst r
    rw [hv i j hij hgap, mul_zero]
  · by_cases hjr : j < r
    · rw [v.property.1 hjr, mul_zero]
    · have hrgap : r.val < i.val + k := lt_of_le_of_lt (le_of_not_gt hjr) hgap
      rw [hu i r hr hrgap, zero_mul]

 theorem UnitriangularDepth.inv {k : ℕ} {u : Unitriangular n R}
    (hu : UnitriangularDepth k u) : UnitriangularDepth k u⁻¹ := by
  classical
  intro i j hij hgap
  have heq : (u.val : Matrix (Fin n) (Fin n) R) *
    (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) = 1 := u.val.val_inv
  have hb : (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R).BlockTriangular id :=
    (u.property.inv u.val).1
  have hd := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) heq
  have hs : ((u.val : Matrix (Fin n) (Fin n) R) *
      (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R)) i j =
      (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) i j := by
    rw [Matrix.mul_apply]
    calc
      _ = (u.val : Matrix (Fin n) (Fin n) R) i i *
          (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) i j := by
        apply Finset.sum_eq_single i
        · intro r _ hri
          rcases lt_or_gt_of_ne hri with hr | hr
          · rw [u.property.1 hr, zero_mul]
          · by_cases hjr : j < r
            · rw [hb hjr, mul_zero]
            · have hrgap : r.val < i.val + k := lt_of_le_of_lt (le_of_not_gt hjr) hgap
              rw [hu i r hr hrgap, zero_mul]
        · simp
      _ = _ := by rw [u.property.2, one_mul]
  rw [hs, Matrix.one_apply_ne (ne_of_lt hij)] at hd
  exact hd

 def unitriangularDepthSubgroup (n k : ℕ) (R : Type*) [CommRing R] :
    Subgroup (Unitriangular n R) where
  carrier := {u | UnitriangularDepth k u}
  one_mem' := unitriangularDepth_one k
  mul_mem' hu hv := hu.mul hv
  inv_mem' hu := hu.inv

 theorem unitriangularDepth_transvection (k : ℕ) (i j : Fin n) (hij : i < j)
    (hgap : i.val + k ≤ j.val) (c : R) :
    UnitriangularDepth k (unitriangularTransvection i j hij c) := by
  intro a b hab habgap
  change Matrix.transvection i j c a b = 0
  have hne : ¬(i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge hgap) habgap
  simp [Matrix.transvection, Matrix.single, Matrix.one_apply_ne (ne_of_lt hab), hne]

 theorem unitriangularDepth_antitone {k l : ℕ} (hkl : k ≤ l) :
    unitriangularDepthSubgroup n l R ≤ unitriangularDepthSubgroup n k R := by
  intro u hu i j hij hgap
  exact hu i j hij (lt_of_lt_of_le hgap (Nat.add_le_add_left hkl i.val))

 theorem unitriangularDepth_terminal {k : ℕ} (hnk : n ≤ k) :
    unitriangularDepthSubgroup n k R = ⊥ := by
  apply le_antisymm
  · intro u hu
    apply Subgroup.mem_bot.mpr
    apply unitriangular_val_injective
    ext i j
    change (u.val : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hu i j hij (by omega), Matrix.one_apply_ne (ne_of_lt hij)]
    · simpa using u.property.2 i
    · rw [u.property.1 hji, Matrix.one_apply_ne (ne_of_gt hji)]
  · exact bot_le

end Hindman168
