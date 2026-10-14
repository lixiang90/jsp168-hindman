import Hindman168.NativeOriginalResidueLocalHaar
import Hindman168.IntegerResidueProgressionEnumeration
import Hindman168.ScalarUnitCubeMean

/-! The original local progression law on ACTUAL interval residue sets.
Their exact enumeration and a proved discrepancy of at most one give the
required positive-fraction length; no cardinality oracle or tail loss. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_interval_local_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ beta ε : ℝ, 0 < ε → ∃ radius : ℝ, 0 < radius ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ᶠ n in atTop,
        ∀ A : ℤ, ∀ T : ℕ, κ*L n ≤ T →
          (∀ z ∈ integerWindow A T, |(z : ℝ)/L n-beta| < radius) →
          ∀ r : Fin M, ∀ f ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
            ‖finiteComplexSetMean (intervalResidueSet A T M r.val)
              (fun z => f (P n (z : ℝ) : D.G ⧸ D.Γ)) -
              ∫ y, f y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)‖ < ε := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta ε hε
  obtain ⟨radius,hr,hprog⟩ := hlaw beta ε hε
  refine ⟨radius,hr,?_⟩
  intro κ hκ hκ1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let τ : ℝ := κ/(2*M)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he := hprog (M : ℤ) (by exact_mod_cast hM.ne') (dvd_refl _) τ hτ hτ1
  filter_upwards [he,hL.eventually_ge_atTop (2*(M : ℝ)/κ),hL.eventually (eventually_gt_atTop 0)]
    with n hn hLarge hLn
  intro A T hT hloc r f hf
  obtain ⟨a,m,hImage,hCard,hMean⟩ := integer_residue_interval_progression A (A+(T : ℤ)) M hM
    (by omega) r
  simp only [add_sub_cancel_left, Int.toNat_natCast] at hImage hCard hMean
  have hCount := (abs_le.mp (interval_residue_count A T hM r.isLt)).1
  rw [hCard] at hCount
  have hScale : 2*(M : ℝ) ≤ L n*κ := (div_le_iff₀ hκ).mp hLarge
  have hm : τ*L n ≤ m := by
    have hCount' : (T : ℝ)/(M : ℝ)-1 ≤ m := by linarith
    have hMultiply := (div_le_iff₀ hMR).mp (show (T : ℝ)/(M : ℝ) ≤ (m : ℝ)+1 by linarith)
    have hτeq : τ*(2*(M : ℝ)) = κ := by dsimp [τ]; exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := (mul_pos hτ hLn).trans_le hm
    exact_mod_cast this
  have ha : a ∈ intervalResidueSet A T M r.val := by
    rw [hImage]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_Ico.mpr ⟨le_rfl,by exact_mod_cast hm0⟩,by simp⟩
  have hres : signedPeriodResidue M hM a = r := by
    apply Fin.ext
    have haMod := (Finset.mem_filter.mp ha).2
    have hz := signed_period_residue_cast M hM a
    rw [haMod] at hz
    exact_mod_cast hz
  have hSample : ∀ x ∈ scalarMvIntegerCube Unit m,
      |((a+(M : ℤ)*x () : ℤ) : ℝ)/L n-beta| < radius := by
    intro x hx
    have hxAll : ∀ i, x i ∈ Finset.Ico 0 (m : ℤ) := by
      simpa only [scalarMvIntegerCube, Fintype.mem_piFinset] using hx
    have hx0 := hxAll ()
    have hxR : a+(M : ℤ)*x () ∈ intervalResidueSet A T M r.val := by
      rw [hImage]
      exact Finset.mem_image.mpr ⟨x (),hx0,rfl⟩
    exact hloc _ (Finset.mem_filter.mp hxR).1
  have hb := hn a m hm hSample f hf
  simp only [hres] at hb
  rw [hMean (fun z => f (P n (z : ℝ) : D.G ⧸ D.Γ))]
  rw [scalar_unit_integer_cube_mean] at hb
  exact hb

end Hindman168
