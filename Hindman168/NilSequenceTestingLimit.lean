import Hindman168.NilTestingMasterGeometry
import Hindman168.NilRootPairingEstimate

/-! Original-law nilsequence testing: one finite recipe family is fixed
at the requested accuracy, then one positive scale is fixed for that
family, and only then the actual master stage tends to infinity. -/

namespace Hindman168
open Filter
open FiniteMass
open NNReal
open scoped BigOperators Topology Classical

noncomputable def piecewiseLinearNilsequence {G : Type*} [Group G]
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (w : ℕ) (y : ℤ) : ℝ :=
  let p := intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y
  obs w p (pieceLinearOrbit Γ (F.modulus w : ℕ) (g w) (x w) p y)

theorem piecewiseLinearNilsequence_abs_le {G : Type*} [Group G]
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (B : ℝ) (hB : ∀ w p z, |obs w p z| ≤ B) (w : ℕ) (y : ℤ) :
    |piecewiseLinearNilsequence Γ F gap obs g x w y| ≤ B := hB w _ _

theorem upperFaceCubeGroup_original_nilsequence_testing
    {G : Type*} [Group G] {d n N m : ℕ} (hd : 0 < d)
    (fil : ℕ → Subgroup G) (hfil : CubeGroupFiltration fil)
    (htop : fil d = ⊥) (hzero : fil 0 = ⊤) (hone : fil 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup fil d)))
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (gap : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val)
    (e : ℕ → ℤ → ℝ)
    (he : ∀ᶠ w in atTop, ∀ y, |e w y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (hdual : ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 d, u.Admissible F C label w →
        |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
          (fun y => e w y * (originalZeroPrimeTemplate (n := n) d gap (fun _ => (0 : Fin 1))).dual
            F (fun _ => J) u w y)| < η)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (B : ℝ) (hB0 : 0 ≤ B) (Lip : ℝ≥0)
    (hB : ∀ w p z, |obs w p z| ≤ B) (hLip : ∀ w p, LipschitzWith Lip (obs w p)) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
      (fun y => e w y * piecewiseLinearNilsequence Γ F gap obs g x w y)) atTop (𝓝 0) := by
  let μ w := integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w)
  let weight w y := 1 + masterPredictionBlockMask F C label w y
  let S := piecewiseLinearNilsequence Γ F gap obs g x
  have hν := hF.block_mask_eventually_nonneg C hN label
  have htotal := hF.nil_testing_weight_eventually_le C hN label gap horder htail
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / 12
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, recipes, select, _C, _hC, hb, ha⟩ :=
    upperFaceCubeGroup_piece_linear_recipe_family fil hfil htop hzero hone Γ hcompact
      (fun wp : ℕ × (ℤ × ℤ) => obs wp.1 wp.2) B Lip
      (fun wp z => hB wp.1 wp.2 z) (fun wp => hLip wp.1 wp.2) δ hδ
  let selected w p := select (w, p)
  let mass : ℝ := ∑ r, (recipes r).coefficientMass
  let bound : ℝ := mass + B
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun r _ => cornerRecipe_coefficientMass_nonneg (recipes r))
  have hbound : 0 ≤ bound := add_nonneg hmass hB0
  let γ : ℝ := ε / (4 * (bound + 1))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨J, hJ, hboundary⟩ := hF.nil_boundary_label_small C hN label gap d horder htail γ hγ
  let piece w := intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ)
  let point w := pieceLinearOrbit Γ (F.modulus w : ℕ) (g w) (x w)
  let choice : ℕ → Fin 1 := fun _ => 0
  let scales : Fin 1 → ℕ := fun _ => J
  let q w y := pieceRecipeZeroDualSum (n := n) recipes (piece w) (selected w) (point w)
    F gap choice scales w y
  let good w y := intervalInteriorRoot (F.gap w (gap w).val)
    (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w : ℕ)) y
  have hpair := pieceRecipeZeroDualSum_pairing_tendsto_zero (n := n) recipes
    (fun r => (hb r).1) piece selected point F gap choice scales C label μ e hν (hdual J hJ)
  have hpairAbs : Tendsto (fun w => |expectation (μ w) (fun y => e w y * q w y)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using hpair.abs
  have hp := hpairAbs.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  filter_upwards [hF.raw_cutoffs_valid, hν, htotal, he, hboundary, hp,
    hF.nil_shift_window_eventually_positive gap J hJ] with w hv hn ht hew hbd hpd hT
  rw [Real.dist_eq, sub_zero]
  have hroot : (C w).pivot (label w) < N := ((C w).pivotIndex (hN w) (label w)).isLt
  have hμ : ∀ y, 0 ≤ μ w y := integerMass_nonneg
    (hv _ (Finset.mem_range.mpr hroot)).2.2
  have hexp : 0 < F.exponent w := lt_of_lt_of_le Nat.zero_lt_one (hF.exponent_positive w)
  have hS : ∀ y, |S w y| ≤ B := piecewiseLinearNilsequence_abs_le Γ F gap obs g x B hB w
  have hgood : ∀ y ∈ (μ w).support, good w y → |S w y - q w y| ≤ δ := by
    intro y _ hy
    have h := pieceRecipeOriginalDual_linear_good_root (n := n) Γ recipes (selected w) (obs w)
      (g w) (x w) δ (fun p b₀ b => (ha (w, p) (g w p) (x w p) b₀ b).le)
      F gap choice scales w y hexp hd (hF.gap_positive _ _) hT hy
    change |S w y - q w y| ≤ δ
    rw [abs_sub_comm]
    exact h
  have hestimate := pieceRecipeOriginalDual_weighted_pairing_bound (n := n) recipes (fun r => (hb r).1)
    (piece w) (selected w) (point w) F gap choice scales w hexp hT (μ w) hμ (e w) (weight w) (S w)
    (fun y _ => by dsimp [weight]; linarith [hn y]) (fun y _ => hew y)
    B hS (good w) δ hδ.le hgood
  have hbad : expectation (μ w) (fun y => if good w y then 0 else weight w y) < γ := by
    have hf : (fun y => if good w y then 0 else weight w y) =
        (fun y => if ¬ good w y then weight w y else 0) := by
      funext y
      by_cases hy : good w y <;> simp [hy]
    rw [hf]
    exact hbd
  have hδtotal : δ * expectation (μ w) (weight w) ≤ 3 * δ := by
    have hh := mul_le_mul_of_nonneg_left ht hδ.le
    simpa only [mul_comm] using hh
  have hboundaryCost : bound * expectation (μ w) (fun y => if good w y then 0 else weight w y) ≤ bound * γ :=
    mul_le_mul_of_nonneg_left hbad.le hbound
  have hγid : (bound + 1) * γ = ε / 4 := by dsimp [γ]; field_simp
  have hsmall : bound * γ < ε / 4 := by nlinarith
  have hδid : 3 * δ = ε / 4 := by dsimp [δ]; ring
  change |expectation (μ w) (fun y => e w y * S w y)| < ε
  change |expectation (μ w) (fun y => e w y * S w y)| ≤
    |expectation (μ w) (fun y => e w y * q w y)| + δ * expectation (μ w) (weight w) +
      bound * expectation (μ w) (fun y => if good w y then 0 else weight w y) at hestimate
  linarith

end Hindman168
