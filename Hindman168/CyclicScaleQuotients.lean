import Hindman168.CyclicShortCubeBound

namespace Hindman168

theorem cyclicScale_factorization (M P R : ℕ) (hM : 0 < M) (hP : 0 < P)
    (hMP : M ∣ P) (hPR : P ∣ R) : R / M = (P / M) * (R / P) := by
  obtain ⟨q, rfl⟩ := hMP
  obtain ⟨n, rfl⟩ := hPR
  rw [Nat.mul_div_cancel_left n hP, Nat.mul_div_cancel_left q hM,
    mul_assoc, Nat.mul_div_cancel_left (q * n) hM]

theorem cyclicScale_quotient_dvd (M P R : ℕ) (hM : 0 < M) (hP : 0 < P)
    (hMP : M ∣ P) (hPR : P ∣ R) : P / M ∣ R / M :=
  ⟨R / P, cyclicScale_factorization M P R hM hP hMP hPR⟩

theorem cyclicScale_short_length (R P J : ℕ) : (R / P) / J = R / (J * P) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm P J]

theorem cyclicScale_subgroup_card (M P R : ℕ) (hM : 0 < M) (hP : 0 < P) (hR : 0 < R)
    (hMP : M ∣ P) (hPR : P ∣ R)
    [Fintype (multipleAddSubgroup (ZMod (R / M)) (P / M))] :
    Fintype.card (multipleAddSubgroup (ZMod (R / M)) (P / M)) = R / P := by
  have hq : 0 < P / M := Nat.div_pos (Nat.le_of_dvd hP hMP) hM
  have hn : 0 < R / P := Nat.div_pos (Nat.le_of_dvd hR hPR) hP
  have hf := cyclicScale_factorization M P R hM hP hMP hPR
  have hm : 0 < R / M := by rw [hf]; exact Nat.mul_pos hq hn
  rw [multipleDivisorSubgroup_card (R / M) (P / M) hm hq
    (cyclicScale_quotient_dvd M P R hM hP hMP hPR), hf,
    Nat.mul_div_cancel_left (R / P) hq]

end Hindman168
