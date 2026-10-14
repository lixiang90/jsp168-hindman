import Hindman168.NativeOriginalIntervalLocalHaar
import Hindman168.NativeRationalLayerHaarContinuity
import Hindman168.RealMeshResiduePartition
import Hindman168.CompactGaugeFiniteOscillation
import Hindman168.ComplexTaggedMeshIntegral

/-! ONE actual finite mesh simultaneously controls original residue-cell
means and approximates all residue Haar integrals for a fixed observable.
The mesh and tags are selected before every eventual length threshold. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_tagged_point_mesh {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h)
    (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ J ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ ε : ℝ, 0 < ε →
      let g : Fin M → ℝ → ℂ := fun r beta =>
        ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)
      ∃ N : ℕ, 0 < N ∧ ∃ tag : Fin N → Icc (0 : ℝ) 1,
        (∀ r : Fin M, ‖(∫ beta in (0 : ℝ)..1, g r beta) -
          (∑ i : Fin N, g r (tag i))/(N : ℂ)‖ ≤ ε) ∧
        ∀ᶠ n in atTop, ∀ i : Fin N, ∀ r : Fin M,
          ‖finiteComplexSetMean (realMeshResidueCell (L n) N M i r)
            (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ)) - g r (tag i)‖ < ε := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro J hJ ε hε
  dsimp only
  let g : Fin M → ℝ → ℂ := fun r beta =>
    ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)
  have hg (r : Fin M) : Continuous (g r) :=
    native_rational_layer_haar_integral_continuous D H 0 (sigma r) (hRat r) h hh J
  choose radius hr hw using fun beta : Icc (0 : ℝ) 1 =>
    native_original_interval_local_haar D H L hL P M hM sigma hRat h hlaw beta ε hε
  obtain ⟨N,hN,tag,htags⟩ := compact_gauge_finite_oscillation radius hr g hg ε hε
  refine ⟨N,hN,tag,?_,?_⟩
  · intro r
    exact complex_tagged_mesh_integral_error N hN (fun i => (tag i : ℝ)) (g r) (hg r) ε
      (fun i t ht => ((htags i t ht).2 r).le)
  · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    let κ : ℝ := 1/(2*N)
    have hκ : 0 < κ := by dsimp [κ]; positivity
    have hκ1 : κ ≤ 1 := by
      dsimp [κ]
      apply (div_le_one (by positivity)).mpr
      linarith
    have hall := Filter.eventually_all.mpr (fun i : Fin N => hw (tag i) κ hκ hκ1)
    filter_upwards [hall,hL.eventually_ge_atTop (2*N),hL.eventually (eventually_gt_atTop 0)]
      with n hn hLarge hLn
    intro i r
    let a : ℝ := (i.val : ℝ)/(N : ℝ)*L n
    let b : ℝ := ((i.val : ℝ)+1)/(N : ℝ)*L n
    have hwidth : b-a = L n/(N : ℝ) := by dsimp [a,b]; ring
    have hab : a ≤ b := by rw [← sub_nonneg, hwidth]; positivity
    have hT : κ*L n ≤ realIntegerIntervalLength a b := by
      have he := (abs_lt.mp (real_integer_interval_length_error a b hab)).1
      rw [hwidth] at he
      have htwo : 2 ≤ L n/(N : ℝ) := (le_div_iff₀ hNR).mpr hLarge
      have heκ : κ*L n = (L n/(N : ℝ))/2 := by dsimp [κ]; ring
      rw [heκ]
      linarith
    have hloc : ∀ z ∈ integerWindow ⌈a⌉ (realIntegerIntervalLength a b),
        |(z : ℝ)/L n-(tag i : ℝ)| < radius (tag i) := by
      intro z hz
      obtain ⟨hz0,hz1⟩ := (real_integer_interval_mem a b hab z).mp hz
      have hzI : (z : ℝ)/L n ∈ Icc ((i.val : ℝ)/N) (((i.val : ℝ)+1)/N) :=
        ⟨(le_div_iff₀ hLn).mpr hz0,((div_lt_iff₀ hLn).mpr hz1).le⟩
      exact (htags i ((z : ℝ)/L n) hzI).1
    exact hn i ⌈a⌉ (realIntegerIntervalLength a b) hT hloc r J hJ

end Hindman168
