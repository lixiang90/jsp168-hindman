import Hindman168.UnitTorusLinearObservableInverse

/-! Genuine affine-basepoint inverse on SAME range samples and canonical
Haar. Actual Fourier basepoint phase has norm ONE and cancels exactly. -/
namespace Hindman168
open scoped BigOperators Classical

theorem unit_torus_fourier_point_add {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (x y : UnitAddTorus ι) :
    UnitAddTorus.mFourier k (x+y)=UnitAddTorus.mFourier k x*UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,smul_add,
    AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

theorem unit_torus_affine_point_norm {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (x : UnitAddTorus ι) : ‖UnitAddTorus.mFourier k x‖=1 := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,
    Circle.norm_coe,Finset.prod_const_one]

theorem unit_torus_affine_fourier_mean_norm {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (u : UnitAddTorus ι) (γ : ι → ℝ) (N : ℕ) :
    ‖finiteComplexSetMean (Finset.range N) (fun n => UnitAddTorus.mFourier k
      (u+(fun i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle))))‖ =
      ‖finiteComplexSetMean (Finset.range N) (fun n =>
        (AddCircle.toCircle (((n : ℝ)*(∑ i, (k i : ℝ)*γ i) : ℝ) : UnitAddCircle) : ℂ))‖ := by
  simp_rw [unit_torus_fourier_point_add,unit_torus_linear_fourier_phase]
  have he : finiteComplexSetMean (Finset.range N) (fun n => UnitAddTorus.mFourier k u*
      (AddCircle.toCircle (((n : ℝ)*(∑ i, (k i : ℝ)*γ i) : ℝ) : UnitAddCircle) : ℂ)) =
      UnitAddTorus.mFourier k u*finiteComplexSetMean (Finset.range N) (fun n =>
        (AddCircle.toCircle (((n : ℝ)*(∑ i, (k i : ℝ)*γ i) : ℝ) : UnitAddCircle) : ℂ)) := by
    dsimp only [finiteComplexSetMean]
    rw [← Finset.mul_sum]
    ring
  rw [he,norm_mul,unit_torus_affine_point_norm,one_mul]

theorem unit_torus_affine_observable_inverse (ι : Type*) [Fintype ι]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (γ : ι → ℝ) (u : UnitAddTorus ι) (N : ℕ), 0 < N →
      ∀ F ∈ unitLipschitzObservables (UnitAddTorus ι),
        δ ≤ ‖unitTorusFiniteDiscrepancy (Finset.range N)
          (fun n => u+(fun i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle))) F‖ →
          ∃ k : ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
            (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨η,hη,_,K,_,hselect⟩ := unit_torus_compact_observable_phase_selection ι
    (unitLipschitzObservables (UnitAddTorus ι)) (unit_lipschitz_observables_compact _) δ hδ
  let A := K+⌈1/(2*η)⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hKA : K ≤ A := by dsimp only [A]; omega
  have hBA : 1/(2*η) ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈1/(2*η)⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A,hA,?_⟩
  intro γ u N hN F hF hbad
  obtain ⟨k,hk,hsize,hmean⟩ := hselect (Finset.range N) (Finset.nonempty_range_iff.mpr hN.ne')
    (fun n => u+(fun i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle))) F hF hbad
  rw [unit_torus_affine_fourier_mean_norm] at hmean
  have hbound := unit_circle_large_linear_mean_inverse (∑ i, (k i : ℝ)*γ i) N hN η hη hmean
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (N : ℝ)*(1/(2*η*(N : ℝ)))=1/(2*η) := by field_simp
  exact ⟨k,hk,hsize.trans hKA,(mul_le_mul_of_nonneg_left hbound hn.le).trans (he.le.trans hBA)⟩

end Hindman168
