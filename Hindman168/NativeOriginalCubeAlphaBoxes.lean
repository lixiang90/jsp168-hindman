import Hindman168.NativeOriginalCubeLocalHaar
import Hindman168.CubeLocalBoxGeometry

/-! Explicit alpha-scale real boxes, correctly rounded to integer progressions.
For each fixed alpha and modulus, the length limit is taken before alpha shrinks. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeCubeAlphaHaarLaw {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) : Prop :=
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta c C : ℝ, 0 < c → 0 ≤ C → ∀ ε : ℝ, 0 < ε →
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 < α → α < α0 →
      ∀ t : ℕ, 0 < t → (M : ℤ) ∣ (t : ℤ) →
      ∀ᶠ m in atTop, ∀ q : Fin (s+2), ∀ lo hi : Fin (q.val+1) → ℝ, ∀ v : Fin (q.val+1) → ℤ,
        (∀ i : Fin q.val, (M : ℤ) ∣ v i.succ) →
        (∀ j, c*α*L m ≤ hi j-lo j ∧ hi j-lo j ≤ C*α*L m) →
        (|lo 0-beta*L m| ≤ C*α*L m ∧ |hi 0-beta*L m| ≤ C*α*L m) →
        (∀ i : Fin q.val, |lo i.succ| ≤ C*α*L m ∧ |hi i.succ| ≤ C*α*L m) →
        ∀ f ∈ unitLipschitzObservables (Finset (Fin q.val) → D.G ⧸ D.Γ),
          ‖finiteComplexSetMean (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t)
            (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) -
            ∫ y, f y ∂nativeResidueCubeHaarImage D H
              (sigma (signedPeriodResidue M hM (v 0))) (hRat _)
              q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)‖ < ε

theorem native_cube_local_to_alpha_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G)
    (hL : Tendsto L atTop atTop) (hlaw : NativeCubeLocalHaarLaw D H L P M hM sigma hRat h) :
    NativeCubeAlphaHaarLaw D H L P M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta c C hc hC ε hε
  obtain ⟨radius,hr,hloc⟩ := hlaw beta ε hε
  let K : ℝ := ((s : ℝ)+2)*(C+1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min 1 (radius/K),lt_min zero_lt_one (div_pos hr hK),?_⟩
  intro α hα hα0 t ht hMt
  have hα1 : α ≤ 1 := (lt_min_iff.mp hα0).1.le
  have hαr : K*α < radius := by
    have hh := (lt_div_iff₀ hK).mp (lt_min_iff.mp hα0).2
    simpa only [mul_comm] using hh
  have hδ : 0 ≤ C*α := mul_nonneg hC hα.le
  have hδC : C*α ≤ C := by nlinarith
  let R : ℝ := |beta|+C+2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have ha : 0 < c*α/2 := by positivity
  have hq := hloc t ht hMt (c*α/2) R ha hR
  filter_upwards [hq,hL.eventually_ge_atTop 1,hL.eventually_ge_atTop (2/(c*α))] with m hm hLm hlarge
  intro q lo hi v hv hlen hbase hinc f hf
  have hLm0 : 0 < L m := by linarith
  have hlarge' : 2 ≤ c*α*L m := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hc hα)).mp hlarge
  have hlength : ∀ j, (c*α/2)*L m ≤ (⌈hi j⌉ : ℝ)-(⌈lo j⌉ : ℝ) ∧
      (⌈hi j⌉ : ℝ)-(⌈lo j⌉ : ℝ) ≤ R*L m := by
    intro j
    have hj := cube_local_ceil_side_bounds (lo j) (hi j) (L m) (c*α) (C*α) hLm hlarge' (hlen j)
    refine ⟨hj.1,hj.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hLm0.le
    dsimp only [R]
    linarith [abs_nonneg beta]
  have hb := cube_local_ceil_endpoint_bound lo hi beta (L m) (C*α) hLm hbase hinc
  have hend : ∀ j, |(⌈lo j⌉ : ℝ)| ≤ R*L m ∧ |(⌈hi j⌉ : ℝ)| ≤ R*L m := by
    intro j
    have hle : (|beta|+C*α+1)*L m ≤ R*L m := by
      apply mul_le_mul_of_nonneg_right _ hLm0.le
      dsimp only [R]
      linarith
    exact ⟨(hb j).1.trans hle,(hb j).2.trans hle⟩
  have hvloc : ∀ x ∈ alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t,
      ∀ V : Finset (Fin q.val), |((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ)/L m-beta| < radius := by
    intro x hx V
    have hv' := cube_local_ceil_vertex_bound lo hi v x t beta (L m) (C*α) hLm0 hδ hbase hinc hx V
    have hdim : (q.val : ℝ)+1 ≤ (s : ℝ)+2 := by exact_mod_cast q.isLt
    have hcoef : ((q.val : ℝ)+1)*(C*α) ≤ K*α := by
      dsimp only [K]
      have h1 := mul_le_mul_of_nonneg_right hdim hδ
      have h2 := mul_nonneg (show 0 ≤ (s : ℝ)+2 by positivity) hα.le
      nlinarith
    exact hv'.trans_lt (hcoef.trans_lt hαr)
  exact hm q (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v hv hlength hend hvloc f hf

end Hindman168
