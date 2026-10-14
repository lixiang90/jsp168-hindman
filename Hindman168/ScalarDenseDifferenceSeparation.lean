import Hindman168.ScalarDenseDifferenceWeightedCoefficients
import Hindman168.ModOneNaturalMultiplier

/-! ONE actual common natural multiplier controls EVERY higher nonlinear
coefficient at its ORIGINAL N^-degree scale. All budgets precede P,Q,sigma,N. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_dense_difference_separation (D : ℕ) (δ A : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) :
    ∃ S T : ℕ, 0 < S ∧ 0 < T ∧
      ∀ P Q : ℝ[X], Q.natDegree ≤ D → ∀ (σ : ℕ → ℝ) (N : ℕ), T ≤ N →
        ∀ U : Finset ℕ, U ⊆ Finset.range N → δ*(N : ℝ) ≤ U.card →
        (∀ h ∈ U, (N : ℝ)^2*‖((scalarDifferencePolynomial P Q h (σ h)).coeff 2 : UnitAddCircle)‖ ≤ A) →
        ∃ M : ℕ, 0 < M ∧ M ≤ S ∧ ∀ j : ℕ, 3 ≤ j → j ≤ D →
          (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ (S : ℝ)*A := by
  obtain ⟨B,T,hB,hT,hInv⟩ := scalar_dense_difference_weighted_coefficients D δ A hδ hδ1 hA
  let I := Finset.Icc 3 D
  let L : ℕ := 1+∑ j ∈ I, j.choose 2
  let K : ℕ := B*L+1
  let S : ℕ := K^(I.card+1)
  have hL : 0 < L := by dsimp [L]; omega
  have hK : 0 < K := by dsimp [K]; omega
  have hBK : B ≤ K := by
    have hm := Nat.mul_le_mul_left B (show 1 ≤ L from hL)
    dsimp [K]
    omega
  refine ⟨S,T,by dsimp [S]; positivity,hT,?_⟩
  intro P Q hQ σ N hTN U hU hdense hcoeff
  obtain ⟨q,hq,hqB,hWeighted⟩ := hInv P Q hQ σ N hTN U hU hdense hcoeff
  have hN : 0 < N := hT.trans_le hTN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let d : ↥I → ℕ := fun j => q*j.val.choose 2
  have hdpos : ∀ j : ↥I, 0 < d j := by
    intro j
    have hj := (Finset.mem_Icc.mp j.property).1
    exact Nat.mul_pos hq (Nat.choose_pos (by omega))
  have hdK : ∀ j : ↥I, d j ≤ K := by
    intro j
    have hs : j.val.choose 2 ≤ L := by
      have he := Finset.single_le_sum (fun k (_ : k ∈ I) => Nat.zero_le (k.choose 2)) j.property
      dsimp [L]
      omega
    exact (Nat.mul_le_mul hqB hs).trans (Nat.le_add_right (B*L) 1)
  obtain ⟨M,hM,hMS,hCommon⟩ := finite_mod_one_common_multiplier d K hK hdpos hdK
  refine ⟨M,hM,by simpa only [S,Fintype.card_coe] using hMS,?_⟩
  intro j hj hjD
  let r : ↥I := ⟨j,Finset.mem_Icc.mpr ⟨hj,hjD⟩⟩
  have hpow : 0 < (N : ℝ)^j := pow_pos hNr j
  have hε : 0 ≤ A/(N : ℝ)^j := by positivity
  have hw : ‖(((d r : ℕ) : ℝ)*Q.coeff j : UnitAddCircle)‖ ≤
      (K : ℝ)*(A/(N : ℝ)^j) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hpow).mpr
    have he := hWeighted j hj hjD
    dsimp only [d,r]
    rw [Nat.cast_mul]
    have hb : (B : ℝ)*A ≤ (K : ℝ)*A := mul_le_mul_of_nonneg_right (by exact_mod_cast hBK) hA
    simpa only [mul_assoc,mul_comm] using he.trans hb
  have hc := hCommon r (Q.coeff j) (A/(N : ℝ)^j) hε hw
  have hbound : ‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ (S : ℝ)*A/(N : ℝ)^j := by
    simpa only [S,Fintype.card_coe,mul_div_assoc] using hc
  simpa only [mul_comm] using (le_div_iff₀ hpow).mp hbound

end Hindman168
