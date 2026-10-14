import Hindman168.LeibmanSimultaneousDirectionReconstruction
import Hindman168.ScalarMvHomogeneousIndices
import Hindman168.FiniteCoefficientScaleTransfer

/-! ALL positive original scalar monomial coefficients are reconstructed
from TRUE homogeneous line constants on enough ACTUAL directions, using
ONE positive bounded natural multiplier across EVERY degree. Original
length scaling is explicit; no direction-dependent character is substituted. -/
namespace Hindman168
open scoped BigOperators Classical

theorem leibman_complete_directional_coefficients (n d K : ℕ) (hK : 0 < K) :
    ∃ C : ℕ, 0 < C ∧ ∀ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range K) → d*K^n < T.card*K →
      ∃ D : ℕ, 0 < D ∧ D ≤ C ∧
      ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ d → ∀ (M N H : ℕ) (A τ : ℝ),
        0 < H → 0 ≤ A → 0 < τ → τ ≤ 1 → τ*(N : ℝ) ≤ H →
        (∀ q ∈ T, ∀ r : ℕ, 0 < r → r ≤ d →
          ‖(((M : ℝ)*MvPolynomial.coeff 0
            (scalarMvLineCoefficient P (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤
            A/(H : ℝ)^r) →
        ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖((((D*M : ℕ) : ℝ)*
            MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) P : ℝ) : UnitAddCircle)‖ ≤
            (C : ℝ)*A*(τ⁻¹)^d := by
  let J (r : Fin d) := scalarMvHomogeneousIndices (Fin n) (r.val+1)
  have hJ (r : Fin d) (I : Fin n → ℕ) (hI : I ∈ J r) : (∑ j, I j) ≤ d := by
    have h := (scalar_mv_homogeneous_indices_mem (r.val+1) I).mp hI
    omega
  obtain ⟨C,hC,hReconstruct⟩ := leibman_simultaneous_direction_coefficient_bound J d hJ K hK
  refine ⟨C,hC,?_⟩
  intro T hT hDense
  obtain ⟨D,hD,hDC,hAll⟩ := hReconstruct T hT hDense
  refine ⟨D,hD,hDC,?_⟩
  intro P hP M N H A τ hH hA hτ hτ1 hLength hLines I hI
  by_cases hid : (∑ j, I j) ≤ d
  · let r : Fin d := ⟨(∑ j, I j)-1,by omega⟩
    have hr : r.val+1=∑ j, I j := by dsimp only [r]; omega
    have hMem : I ∈ J r := (scalar_mv_homogeneous_indices_mem (r.val+1) I).mpr hr.symm
    let a (i : ↥(J r)) := (M : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm i.val) P
    have hValues (q : ↥T) :
        ‖((∑ i : ↥(J r), a i*leibmanMonomialVector (J r) (fun j => (q.val j : ℝ)) i : ℝ) : UnitAddCircle)‖ ≤
          A/(H : ℝ)^(∑ j, I j) := by
      have he : (∑ i : ↥(J r), a i*leibmanMonomialVector (J r) (fun j => (q.val j : ℝ)) i) =
          (M : ℝ)*MvPolynomial.coeff 0 (scalarMvLineCoefficient P (fun j => (q.val j : ℝ)) (r.val+1)) := by
        rw [scalar_mv_line_constant_monomial_vector,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [a,J]
        ring
      rw [he,hr]
      exact hLines q.val q.property _ hI hid
    have hCoeff := hAll r a (A/(H : ℝ)^(∑ j, I j)) (by positivity) hValues ⟨I,hMem⟩
    change ‖(((D : ℝ)*((M : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) P) : ℝ) :
      UnitAddCircle)‖ ≤ (C : ℝ)*(A/(H : ℝ)^(∑ j, I j)) at hCoeff
    have hBound : (H : ℝ)^(∑ j, I j)*‖((((D*M : ℕ) : ℝ)*
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) P : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ)*A := by
      rw [Nat.cast_mul,mul_assoc]
      have h := mul_le_mul_of_nonneg_left hCoeff (by positivity : 0 ≤ (H : ℝ)^(∑ j, I j))
      have hEq : (H : ℝ)^(∑ j, I j)*((C : ℝ)*(A/(H : ℝ)^(∑ j, I j)))=(C : ℝ)*A := by
        field_simp
      exact h.trans_eq hEq
    exact finite_coefficient_scale_transfer N H τ ((C : ℝ)*A) _ d (∑ j, I j)
      hτ hτ1 (by positivity) (norm_nonneg _) hLength hid hBound
  · rw [scalar_mv_coefficient_zero_above_degree P d hP I (Nat.lt_of_not_ge hid),
      mul_zero,AddCircle.coe_zero,norm_zero,mul_zero]
    positivity

end Hindman168
