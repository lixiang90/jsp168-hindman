import Hindman168.MaskRemovalPrimeInsertion

/-! Exact integer balanced substitutions and their absorbed branches.
Integer division is used algebraically only under the stated divisibility
or nonzero multiplier hypotheses. -/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def maskBalancedCoordinates {ι : Type*} [DecidableEq ι]
    (u v : ι) (p : ℕ) (z : ι → ℤ) : ι → ℤ :=
  Function.update (Function.update z u (z u / (p : ℤ))) v ((p : ℤ) * z v)

noncomputable def maskAbsorbedCoordinates {ι : Type*} [DecidableEq ι]
    (u v : ι) (p q : ℕ) (z : ι → ℤ) : ι → ℤ :=
  Function.update (Function.update z u ((q : ℤ) * z u)) v ((p : ℤ) * z v)

theorem maskBalancedCoordinates_dilation_cancel {ι : Type*} [DecidableEq ι]
    (u v : ι) (hne : u ≠ v) {p : ℕ} (hp : p ≠ 0) (z : ι → ℤ) :
    maskBalancedCoordinates u v p (Function.update z u ((p : ℤ) * z u)) =
      Function.update z v ((p : ℤ) * z v) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  funext i
  by_cases hiu : i = u
  · subst i
    simp [maskBalancedCoordinates, Function.update_of_ne hne, Int.mul_ediv_cancel_left _ hpZ]
  · by_cases hiv : i = v
    · subst i
      simp [maskBalancedCoordinates, Function.update_of_ne (Ne.symm hne)]
    · simp [maskBalancedCoordinates, Function.update_of_ne hiu, Function.update_of_ne hiv]

theorem maskBalancedCoordinates_pair_dilation {ι : Type*} [DecidableEq ι]
    (u v : ι) (hne : u ≠ v) {p : ℕ} (hp : p ≠ 0) (q : ℕ) (z : ι → ℤ) :
    maskBalancedCoordinates u v p (Function.update z u (((p * q : ℕ) : ℤ) * z u)) =
      maskAbsorbedCoordinates u v p q z := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  funext i
  by_cases hiu : i = u
  · subst i
    simp [maskBalancedCoordinates, maskAbsorbedCoordinates, Function.update_of_ne hne,
      Nat.cast_mul, mul_assoc, Int.mul_ediv_cancel_left _ hpZ]
  · by_cases hiv : i = v
    · subst i
      simp [maskBalancedCoordinates, maskAbsorbedCoordinates, Function.update_of_ne (Ne.symm hne)]
    · simp [maskBalancedCoordinates, maskAbsorbedCoordinates,
        Function.update_of_ne hiu, Function.update_of_ne hiv]

theorem maskBalancedCoordinates_pair_dilation_swapped {ι : Type*} [DecidableEq ι]
    (u v : ι) (hne : u ≠ v) (p : ℕ) {q : ℕ} (hq : q ≠ 0) (z : ι → ℤ) :
    maskBalancedCoordinates u v q (Function.update z u (((p * q : ℕ) : ℤ) * z u)) =
      maskAbsorbedCoordinates u v q p z := by
  rw [Nat.mul_comm p q]
  exact maskBalancedCoordinates_pair_dilation u v hne hq p z

theorem maskBalancedCoordinates_preserves_product {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (u v : ι) (hu : u ∈ U) (hv : v ∈ U) (hne : u ≠ v)
    (p : ℕ) (z : ι → ℤ) (hdiv : (p : ℤ) ∣ z u) :
    (∏ i ∈ U, maskBalancedCoordinates u v p z i) = ∏ i ∈ U, z i := by
  have hue : u ∈ U.erase v := Finset.mem_erase.mpr ⟨hne, hu⟩
  unfold maskBalancedCoordinates
  rw [Finset.prod_update_of_mem hv, Finset.sdiff_singleton_eq_erase,
    Finset.prod_update_of_mem hue, Finset.sdiff_singleton_eq_erase]
  have hp := Int.ediv_mul_cancel hdiv
  calc
    ((p : ℤ) * z v) * ((z u / p) * ∏ i ∈ (U.erase v).erase u, z i) =
        z v * (z u * ∏ i ∈ (U.erase v).erase u, z i) := by
          calc
            _ = z v * ((z u / p * p) * ∏ i ∈ (U.erase v).erase u, z i) := by ring
            _ = _ := by rw [hp]
    _ = ∏ i ∈ U, z i := by
      rw [Finset.mul_prod_erase _ _ hue, Finset.mul_prod_erase _ _ hv]

end Hindman168
