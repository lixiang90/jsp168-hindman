import Hindman168.NativeOriginalIntervalLocalHaar
import Hindman168.RealIntervalResidueGeometry

/-! The q=0 paper windows with exact real endpoints. The epsilon statement
takes the length limit for each FIXED alpha before alpha tends to zero. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeRealLocalHaarLaw {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) : Prop :=
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta ε : ℝ, 0 < ε → ∃ α₀ : ℝ, 0 < α₀ ∧
    ∀ α : ℝ, 0 < α → α < α₀ → ∀ᶠ n in atTop,
      ∀ r : Fin M, ∀ f ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        ‖finiteComplexSetMean (realIntervalResidueSet (beta*L n) ((beta+α)*L n) M r.val)
          (fun z => f (P n (z : ℝ) : D.G ⧸ D.Γ)) -
          ∫ y, f y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)‖ < ε

theorem native_original_real_local_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    NativeRealLocalHaarLaw D H L P M sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta ε hε
  obtain ⟨radius,hr,hint⟩ := native_original_interval_local_haar D H L hL P M hM sigma hRat h hlaw beta ε hε
  refine ⟨min radius 1,lt_min hr zero_lt_one,?_⟩
  intro α hα hα0
  have hαr : α < radius := hα0.trans_le (min_le_left _ _)
  have hα1 : α < 1 := hα0.trans_le (min_le_right _ _)
  have hκ : 0 < α/2 := by positivity
  have hκ1 : α/2 ≤ 1 := by linarith
  filter_upwards [hint (α/2) hκ hκ1,hL.eventually_ge_atTop (2/α),hL.eventually (eventually_gt_atTop 0)]
    with n hn hLarge hLn
  have hab : beta*L n ≤ (beta+α)*L n := by nlinarith
  have hT : (α/2)*L n ≤ realIntegerIntervalLength (beta*L n) ((beta+α)*L n) := by
    have hE := (abs_lt.mp (real_integer_interval_length_error _ _ hab)).1
    have hScale : 2 ≤ L n*α := (div_le_iff₀ hα).mp hLarge
    nlinarith
  have hloc : ∀ z ∈ integerWindow ⌈beta*L n⌉ (realIntegerIntervalLength (beta*L n) ((beta+α)*L n)),
      |(z : ℝ)/L n-beta| < radius := by
    intro z hz
    obtain ⟨hz0,hz1⟩ := (real_integer_interval_mem _ _ hab z).mp hz
    have hlo : beta ≤ (z : ℝ)/L n := (le_div_iff₀ hLn).mpr hz0
    have hhi : (z : ℝ)/L n < beta+α := (div_lt_iff₀ hLn).mpr hz1
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  exact hn ⌈beta*L n⌉ (realIntegerIntervalLength (beta*L n) ((beta+α)*L n)) hT hloc

end Hindman168
