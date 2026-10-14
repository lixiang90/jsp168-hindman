import Hindman168.NativeNoLongBadFamilyStatement
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! ACTUAL original common-character production + finite genuine canonical
kernel budgets give a true lower-finrank induction step. The only IH is the
universal strictly smaller-native-finrank statement. No analytic oracle. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_no_long_bad_family_induction_step {s : ℕ}
    (D : NativeNilmanifoldData.{u} s)
    (hLower : ∀ (D' : NativeNilmanifoldData.{u} s), Module.finrank ℝ D'.E < Module.finrank ℝ D.E →
      NativeNoLongBadFamilyStatement D') : NativeNoLongBadFamilyStatement D := by
  intro n d c C B η Lip hc hC hB hη Scale Z hScale hr
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,hA,hCommon⟩ := native_original_common_bad_family D n d c C B η Lip
    hc (zero_le_one.trans hC) hB hη Scale Z hScale hr
  let Top : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
  let hTop := native_original_top_lie_rational D
  let hHor (χ : ↥S) := hS χ.val χ.property
  let hBracket (χ : ↥S) := native_original_horizontal_top_bracket D χ.val (hHor χ)
  let hRat (χ : ↥S) := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ.val (hHor χ).2.2
  have hGeometry (χ : ↥S) := native_original_actual_horizontal_kernel_descent (κ := Fin n)
    D χ.val (hHor χ) d A C B hA hC hB Lip c η hc hη Scale Z hScale hr
  choose V hVr hVS hV K hK hPeriod Part L hPart hStage using hGeometry
  let Family (χ : ↥S) (j : Fin (K χ)) := roughNativeKernelNilmanifold D Top hTop χ.val
    (hBracket χ) (hRat χ) (V χ) (hVr χ) (j.val : ℤ)
  have hRank (χ : ↥S) (j : Fin (K χ)) : Module.finrank ℝ (Family χ j).E < Module.finrank ℝ D.E :=
    roughNativeKernelNilmanifold_finrank_lt D Top hTop χ.val (hBracket χ) (hRat χ)
      (V χ) (hVr χ) (j.val : ℤ) (hVS χ) (by rw [hV χ]; norm_num)
  have hChild (χ : ↥S) (j : Fin (K χ)) := hLower (Family χ j) (hRank χ j)
    n (roughKernelDegreeFactor s*d) (c/(4*Part χ)) (max (4*C/Part χ) (C+1)) B (η/4) (L χ)
    (div_pos hc (mul_pos (by norm_num : (0 : ℝ) < 4) (by exact_mod_cast hPart χ)))
    (le_trans (by linarith : 1 ≤ C+1) (le_max_right _ _)) hB (by positivity)
    Scale (fun w => Z w/(K χ)) hScale
    (rough_residue_scale_paper_ratios hr (K χ) (by exact_mod_cast hK χ))
  choose Hchild hHchild hNoChild using hChild
  let H := 1+∑ χ : ↥S, ∑ j : Fin (K χ), Hchild χ j
  have hH : 0 < H := by dsimp only [H]; omega
  have hHbound (χ : ↥S) (j : Fin (K χ)) : Hchild χ j ≤ H := by
    have h1 : Hchild χ j ≤ ∑ j : Fin (K χ), Hchild χ j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j : Fin (K χ), Hchild χ j) ≤ ∑ χ : ↥S, ∑ j : Fin (K χ), Hchild χ j :=
      Finset.single_le_sum (f := fun χ : ↥S => ∑ j : Fin (K χ), Hchild χ j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ χ)
    exact (h1.trans h2).trans (by dsimp only [H]; omega)
  have hNoAll : ∀ᶠ w in atTop, ∀ χ : ↥S, ∀ j : Fin (K χ),
      ¬ RoughNativeBadFamily (κ := Fin n) (Family χ j) H w (Scale w) (Z w/K χ)
        (roughKernelDegreeFactor s*d) (c/(4*Part χ)) (max (4*C/Part χ) (C+1)) (L χ) B (η/4) := by
    apply Filter.eventually_all.mpr
    intro χ
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [hNoChild χ j] with w hw
    exact fun h => hw (rough_native_bad_family_length_mono (Family χ j) (hHbound χ j) h)
  have hLengths (χ : ↥S) := hStage χ H hH
  choose N hN hRun using hLengths
  let M := 1+∑ χ : ↥S, N χ
  have hM : 0 < M := by dsimp only [M]; omega
  have hNbound (χ : ↥S) : N χ ≤ M :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ χ)).trans
      (by dsimp only [M]; omega)
  have hRunAll := Filter.eventually_all.mpr hRun
  obtain ⟨Nparent,hParent,hSelected⟩ := hCommon M hM
  refine ⟨Nparent,hParent,?_⟩
  filter_upwards [hSelected,hRunAll,hNoAll] with w hw hRuns hNo
  intro hBad
  obtain ⟨χ,hχ,Q,p,t,diff,hDegree,hLog,hDiff,hSmooth,hRows⟩ := hw hBad
  let label : ↥S := ⟨χ,hχ⟩
  have hRestricted (z : ℕ) (hz : z < N label) := hRows z (hz.trans_le (hNbound label))
  obtain ⟨j,_hChildRank,hChildBad⟩ := hRuns label Q p hDegree hLog t diff hDiff hSmooth
    (fun z hz => ⟨(hRestricted z hz).1,(hRestricted z hz).2.1⟩)
    (fun z hz => (hRestricted z hz).2.2.1)
    (fun z hz => (hRestricted z hz).2.2.2.1)
    (fun z hz => (hRestricted z hz).2.2.2.2)
  exact hNo label j hChildBad

end Hindman168
