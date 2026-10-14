import Hindman168.TwoLinearRows

/-!
# Actual prime-power systems of integer linear rows

The local map sends the original residue vector to each row modulo its
own required prime power. Its kernel is exactly the simultaneous row
event. The normalized count is at least one, equals one if at most one
valuation is positive and its row is primitive, and is bounded by the
single-row or independent two-row probabilities for the actual law.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primePowerRowSystem (p q d A : ℕ) (a : Fin q → ℕ)
    (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ) :
    (Fin d → ZMod (p ^ A)) →+ (∀ u : Fin q, ZMod (p ^ a u)) where
  toFun x u := ZMod.castHom (pow_dvd_pow p (ha u)) (ZMod (p ^ a u))
    (linearRowAddHom (fun i => (c u i : ZMod (p ^ A))) x)
  map_zero' := by
    funext u
    change ZMod.castHom (pow_dvd_pow p (ha u)) (ZMod (p ^ a u))
      (linearRowAddHom (fun i => (c u i : ZMod (p ^ A))) 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    funext u
    change ZMod.castHom (pow_dvd_pow p (ha u)) (ZMod (p ^ a u))
      (linearRowAddHom (fun i => (c u i : ZMod (p ^ A))) (x + y)) = _
    rw [map_add, map_add]
    rfl

theorem primePowerRowSystem_zero_iff (p q d A : ℕ) (a : Fin q → ℕ)
    (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ) (x : Fin d → ZMod (p ^ A)) :
    primePowerRowSystem p q d A a ha c x = 0 ↔
      ∀ u, ZMod.castHom (pow_dvd_pow p (ha u)) (ZMod (p ^ a u))
        (linearRowAddHom (fun i => (c u i : ZMod (p ^ A))) x) = 0 := by
  exact ⟨fun h u => congrFun h u, fun h => funext h⟩

noncomputable def primePowerLocalAlpha (p q d A : ℕ) [NeZero p]
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ) : ℝ :=
  (p ^ (∑ u, a u) : ℕ) * event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
    (fun x => primePowerRowSystem p q d A a ha c x = 0)

theorem primePowerLocalAlpha_bounds (p q d A : ℕ) [NeZero p]
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ) :
    1 ≤ primePowerLocalAlpha p q d A a ha c ∧
      primePowerLocalAlpha p q d A a ha c ≤ (p ^ (∑ u, a u) : ℕ) :=
  primePower_normalized_kernel_bounds p q d A a (primePowerRowSystem p q d A a ha c)

theorem primePower_reduced_primitive_row_zero_mass {p d A B : ℕ} [NeZero p]
    (hp : p.Prime) (hBA : B ≤ A) (c : Fin d → ℤ) (hrow : ∃ j, (c j : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
        (linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x) = 0) =
      ((p ^ B : ℕ) : ℝ)⁻¹ := by
  obtain ⟨j, hj⟩ := hrow
  let r := ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
  let f := r.toAddMonoidHom.comp (linearRowAddHom (fun i => (c i : ZMod (p ^ A))))
  have hf : Function.Surjective f := (ZMod.castHom_surjective (pow_dvd_pow p hBA)).comp
    (linearRowAddHom_surjective_of_unit _ j (integer_coefficient_unit_primePower hp A (c j) hj))
  have hpush := uniformFintypeMass_addGroup_push f hf
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod (p ^ A))) f
    (fun y : ZMod (p ^ B) => y = 0)
  rw [hpush, uniformFintypeMass_event_eq, ZMod.card] at hmap
  exact hmap.symm

theorem primePowerRowSystem_kernel_le_row {p q d A : ℕ} [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u : Fin q) (hrow : ∃ j, (c u j : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => primePowerRowSystem p q d A a ha c x = 0) ≤ ((p ^ a u : ℕ) : ℝ)⁻¹ := by
  have h := event_mono (uniformFintypeMass (Fin d → ZMod (p ^ A)))
    (uniformFintypeMass_nonneg _) (fun x hx => (primePowerRowSystem_zero_iff p q d A a ha c x).mp hx u)
  rw [primePower_reduced_primitive_row_zero_mass hp (ha u) (c u) hrow] at h
  exact h

theorem primePowerRowSystem_kernel_le_two_rows {p q d A : ℕ} [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u v : Fin q) (j k : Fin d)
    (hminor : ((c u j * c v k - c u k * c v j : ℤ) : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => primePowerRowSystem p q d A a ha c x = 0) ≤
      ((p ^ (a u + a v) : ℕ) : ℝ)⁻¹ := by
  have h : event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => primePowerRowSystem p q d A a ha c x = 0) ≤
      event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
        (fun x => ZMod.castHom (pow_dvd_pow p (ha u)) (ZMod (p ^ a u))
            (linearRowAddHom (fun i => (c u i : ZMod (p ^ A))) x) = 0 ∧
          ZMod.castHom (pow_dvd_pow p (ha v)) (ZMod (p ^ a v))
            (linearRowAddHom (fun i => (c v i : ZMod (p ^ A))) x) = 0) := by
    apply event_mono _ (uniformFintypeMass_nonneg _)
    intro x hx
    exact ⟨(primePowerRowSystem_zero_iff p q d A a ha c x).mp hx u,
      (primePowerRowSystem_zero_iff p q d A a ha c x).mp hx v⟩
  rw [primePower_twoRow_reduced_divisibility_mass hp (ha u) (ha v) (c u) (c v) j k hminor] at h
  exact h

theorem primePower_normalization_cancel (p S T : ℕ) [NeZero p] (hTS : T ≤ S) :
    ((p ^ S : ℕ) : ℝ) * ((p ^ T : ℕ) : ℝ)⁻¹ = ((p ^ (S - T) : ℕ) : ℝ) := by
  have hp : p ^ S = p ^ (S - T) * p ^ T := by rw [← pow_add, Nat.sub_add_cancel hTS]
  have hn : ((p ^ T : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_ne_zero T (NeZero.ne p))
  rw [hp, Nat.cast_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem primePowerLocalAlpha_le_single (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u : Fin q) (hrow : ∃ j, (c u j : ZMod p) ≠ 0) :
    primePowerLocalAlpha p q d A a ha c ≤ ((p ^ ((∑ i, a i) - a u) : ℕ) : ℝ) := by
  have hsum : a u ≤ ∑ i, a i := Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ u)
  unfold primePowerLocalAlpha
  exact (mul_le_mul_of_nonneg_left (primePowerRowSystem_kernel_le_row hp a ha c u hrow)
    (Nat.cast_nonneg _)).trans_eq (primePower_normalization_cancel p _ _ hsum)

theorem primePowerLocalAlpha_le_pair (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u v : Fin q) (j k : Fin d)
    (hminor : ((c u j * c v k - c u k * c v j : ℤ) : ZMod p) ≠ 0) :
    primePowerLocalAlpha p q d A a ha c ≤
      ((p ^ ((∑ i, a i) - (a u + a v)) : ℕ) : ℝ) := by
  have huv : u ≠ v := by
    intro h
    subst v
    simp only [mul_comm (c u j) (c u k), sub_self, Int.cast_zero, ne_eq, not_true_eq_false] at hminor
  have hsum : a u + a v ≤ ∑ i, a i := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({u, v} : Finset (Fin q))) (fun i _ _ => Nat.zero_le (a i))
    simpa only [Finset.sum_pair huv] using h
  unfold primePowerLocalAlpha
  exact (mul_le_mul_of_nonneg_left (primePowerRowSystem_kernel_le_two_rows hp a ha c u v j k hminor)
    (Nat.cast_nonneg _)).trans_eq (primePower_normalization_cancel p _ _ hsum)

theorem primePowerLocalAlpha_all_zero (p q d A : ℕ) [NeZero p]
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ)
    (hz : ∀ u, a u = 0) : primePowerLocalAlpha p q d A a ha c = 1 := by
  have he (x : Fin d → ZMod (p ^ A)) : primePowerRowSystem p q d A a ha c x = 0 := by
    apply (primePowerRowSystem_zero_iff p q d A a ha c x).mpr
    intro u
    letI : Subsingleton (ZMod (p ^ a u)) := by rw [hz u, pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  unfold primePowerLocalAlpha
  have hE : (fun x => primePowerRowSystem p q d A a ha c x = 0) = (fun _ => True) := by
    funext x
    exact propext ⟨fun _ => trivial, fun _ => he x⟩
  rw [hE]
  have ht : event (uniformFintypeMass (Fin d → ZMod (p ^ A))) (fun _ => True) =
      total (uniformFintypeMass (Fin d → ZMod (p ^ A))) := by
    simp only [event, total, if_true]
  rw [ht, uniformFintypeMass_total]
  simp only [hz, Finset.sum_const_zero, pow_zero, Nat.cast_one, mul_one]

theorem primePowerLocalAlpha_single_positive (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (u : Fin q)
    (hother : ∀ v, v ≠ u → a v = 0) (hrow : ∃ j, (c u j : ZMod p) ≠ 0) :
    primePowerLocalAlpha p q d A a ha c = 1 := by
  have hsum : (∑ i, a i) = a u := by
    apply Finset.sum_eq_single u
    · intro v _ hv
      exact hother v hv
    · intro h
      exact (h (Finset.mem_univ u)).elim
  have h1 := (primePowerLocalAlpha_bounds p q d A a ha c).1
  have h2 := primePowerLocalAlpha_le_single p q d A hp a ha c u hrow
  rw [hsum, Nat.sub_self, pow_zero, Nat.cast_one] at h2
  exact le_antisymm h2 h1

end Hindman168
