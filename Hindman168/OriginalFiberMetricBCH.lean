import Hindman168.OriginalFiberMetricCompact
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget

/-! Local metric control for actual BCH subgroup quotients.
The source quotient is compact and its lattice is exactly the inverse image
of the ambient lattice. Both metrics are the official BCH quotient metrics. -/

namespace Hindman168.OriginalFiberMetric

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieBCHGroup
open Set Filter Topology
open scoped NNReal BigOperators

private theorem finite_abs_bound {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ B : ℝ≥0, ∀ i, |a i| ≤ B := by
  classical
  refine ⟨∑ i, ‖a i‖₊, ?_⟩
  intro i
  have h : ‖a i‖₊ ≤ ∑ j, ‖a j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖a j‖₊) (fun j _ => bot_le) (Finset.mem_univ i)
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using
    (show (‖a i‖₊ : ℝ) ≤ ((∑ j, ‖a j‖₊ : ℝ≥0) : ℝ) from h)

section LeftTranslations

variable {ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_lipschitz_left_pair (e : Basis ι ℝ L)
    (a : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    ∃ C : ℝ≥0, 0 < C ∧
      LipschitzWith C (fun x => a * x) ∧ LipschitzWith C (fun x => a⁻¹ * x) := by
  letI := rightMetricSpace (hnil := hnil) e
  have single (g : NilpotentLieBCHGroup L s hnil) :
      ∃ C : ℝ≥0, 0 < C ∧ LipschitzWith C (fun x => g * x) := by
    obtain ⟨B, hB⟩ := finite_abs_bound (fun p : ι × ι =>
      e.repr (g * (⟨e p.1⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord p.2)
    exact ⟨coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B,
      coordinateLipschitzBound_pos _ _ _,
      lipschitz_mul_left_of_basis_bound e g B (fun i k => hB (i, k))⟩
  obtain ⟨C, hC, hc⟩ := single a
  obtain ⟨D, hD, hd⟩ := single a⁻¹
  exact ⟨max C D, hC.trans_le (le_max_left _ _),
    hc.weaken (le_max_left _ _), hd.weaken (le_max_right _ _)⟩

end LeftTranslations

section QuotientEmbedding

variable {G H : Type*} [Group G] [Group H]

theorem cosetMap_injective_of_comap (Γ : Subgroup G) (Λ : Subgroup H)
    (φ : G →* H) (hΓ : Γ = Λ.comap φ) :
    Function.Injective (cosetMap Γ Λ φ hΓ.le) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      apply QuotientGroup.eq.mpr
      have h := QuotientGroup.eq.mp hxy
      simpa only [hΓ, Subgroup.mem_comap, map_mul, map_inv] using h

end QuotientEmbedding

section LocalChart

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

/- The following coordinate estimate is the original OpenAI proof from
`BCHUniformQuotientCharts.lean` at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
reproduced here with a narrower import boundary. -/
theorem quotient_chart_metric_bounds
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z * x) → LipschitzWith C (fun x => z⁻¹ * x) →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l →
        letI := quotientMetricSpace e Γ hΓ
        ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
          let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
          dist (q v) (q w) ≤ (C : ℝ) * (bchBoxMetricConstant s (Fintype.card ι) H 1 : ℝ) * dist v w ∧
          dist v w ≤ (bchInverseBoxConstant s (Fintype.card ι) H 1 : ℝ) * C * dist (q v) (q w) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft hleftInv r hr hr1 hsmall
  let := quotientMetricSpace e Γ hΓ
  intro v w hv hw
  have hC' : (0 : ℝ) < C := hC
  have hR : (C : ℝ) * (Fintype.card ι + 1) * r ≤
      bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    calc
      ((C : ℝ) * (Fintype.card ι + 1) * r) * (4 * C) =
          4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hsmall
  have hball (u : ι → ℝ) (hu : ∀ i, |u i| ≤ r) :
      dist (z * (basisHomeomorph e).symm u) z ≤
        bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    have hlog : dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 ≤ (Fintype.card ι + 1) * r := by
      calc
        _ = dist 1 ((basisHomeomorph (hnil := hnil) e).symm u) := dist_comm _ _
        _ ≤ coordinateL2Norm (basisHomeomorph e ((basisHomeomorph (hnil := hnil) e).symm u)) :=
          dist_one_le_coordinateL2Norm e _
        _ = coordinateL2Norm u := by rw [Homeomorph.apply_symm_apply]
        _ ≤ _ := coordinateL2Norm_le_card_bound u hr hu
    have htrans := hleft.dist_le_mul ((basisHomeomorph (hnil := hnil) e).symm u) 1
    rw [mul_one] at htrans
    calc
      _ ≤ (C : ℝ) * dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 := htrans
      _ ≤ (C : ℝ) * ((Fintype.card ι + 1) * r) := mul_le_mul_of_nonneg_left hlog C.coe_nonneg
      _ = (C : ℝ) * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hR
  have hq := quotient_dist_eq_on_ball_of_lattice_grid e c hstructure hc Γ hΓ l hl hgrid C hC z
    hleftInv (hball v hv) (hball w hw)
  have hv1 (i) : |v i| ≤ (1 : ℝ) := (hv i).trans hr1
  have hw1 (i) : |w i| ≤ (1 : ℝ) := (hw i).trans hr1
  have hforward := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc 1 le_rfl).dist_le_mul v hv1 w hw1
  have hinverse := dist_coordinates_le_bchInverseBoxConstant e c hstructure hc 1 le_rfl
    ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hv1 i)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hw1 i)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hinverse
  dsimp only
  rw [hq]
  constructor
  · apply (hleft.dist_le_mul _ _).trans
    exact (mul_le_mul_of_nonneg_left hforward C.coe_nonneg).trans_eq (by ring)
  · have hback : dist ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w) ≤
        (C : ℝ) * dist (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w) := by
      have hb := hleftInv.dist_le_mul
        (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w)
      rw [inv_mul_cancel_left, inv_mul_cancel_left] at hb
      exact hb
    exact hinverse.trans ((mul_le_mul_of_nonneg_left hback (bchInverseBoxConstant _ _ _ _).coe_nonneg).trans_eq (by ring))


end LocalChart

section MetricEmbedding

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t HE HF : ℕ}
  {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

/-- A split linear BCH inclusion induces an inverse-Lipschitz embedding
of a compact lattice quotient. The lattice is the exact preimage; the
source and ambient metrics are unchanged. -/
theorem exists_cosetMap_antilipschitz
    (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (ce : ι → ι → ι → ℚ) (cf : κ → κ → κ → ℚ)
    (he : ∀ i j k, algebraMap ℚ ℝ (ce i j k) = e.repr ⁅e i, e j⁆ k)
    (hf : ∀ i j k, algebraMap ℚ ℝ (cf i j k) = f.repr ⁅f i, f j⁆ k)
    (hce : ∀ i j k, RationalHeightLE (ce i j k) HE)
    (hcf : ∀ i j k, RationalHeightLE (cf i j k) HF)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hΓclosed : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hL)))
    (hΛclosed : IsClosed (Λ : Set (NilpotentLieBCHGroup M t hM)))
    (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Λ, f.equivFun γ.coord ∈ realDenominatorGrid l)
    (φ : L →ₗ⁅ℝ⁆ M) (ψ : M →ₗ[ℝ] L) (hψ : ∀ x, ψ (φ x) = x)
    (hΓ : Γ = Λ.comap (mapReal (hnil := hL) (hM := hM) φ))
    (hcompact : CompactSpace (NilpotentLieBCHGroup L s hL ⧸ Γ)) :
    letI := quotientMetricSpace e Γ hΓclosed
    letI := quotientMetricSpace f Λ hΛclosed
    ∃ C : ℝ≥0, AntilipschitzWith C (cosetMap Γ Λ (mapReal φ) hΓ.le) := by
  classical
  letI : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ M := f.finiteDimensional_of_finite
  letI := rightMetricSpace (hnil := hL) e
  letI := rightMetricSpace (hnil := hM) f
  letI := rightMetricSpace_isIsometricSMul (hnil := hL) e
  letI := rightMetricSpace_isIsometricSMul (hnil := hM) f
  letI := quotientMetricSpace e Γ hΓclosed
  letI := quotientMetricSpace f Λ hΛclosed
  letI := hcompact
  let F := cosetMap Γ Λ (mapReal (hnil := hL) (hM := hM) φ) hΓ.le
  obtain ⟨Bφ, hBφ⟩ := finite_abs_bound (fun p : κ × ι => f.repr (φ (e p.2)) p.1)
  have hφLip := lipschitz_mapReal_of_entry_bound (hnil := hL) (hM := hM)
    e f φ Bφ (fun k i => hBφ (k, i))
  have hFcont : Continuous F :=
    (lipschitz_cosetMap Γ Λ hΓclosed hΛclosed (mapReal φ) hΓ.le hφLip).continuous
  have hFinj : Function.Injective F := cosetMap_injective_of_comap Γ Λ (mapReal φ) hΓ
  apply exists_antilipschitz_of_compact_local F hFcont hFinj
  let A := basisCoordinateMap e f φ.toLinearMap
  let B := basisCoordinateMap f e ψ
  have hBA (v : ι → ℝ) : B (A v) = v := by
    simp only [A, B, basisCoordinateMap_apply, LinearEquiv.symm_apply_apply]
    change e.equivFun (ψ (φ (e.equivFun.symm v))) = v
    rw [hψ, LinearEquiv.apply_symm_apply]
  have hAanti : AntilipschitzWith ‖B‖₊ A := by
    apply AntilipschitzWith.of_le_mul_dist
    intro v w
    simpa only [hBA] using B.lipschitz.dist_le_mul (A v) (A w)
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨Cs, hCs, hsleft, _⟩ := exists_lipschitz_left_pair e g
    obtain ⟨Ct, hCt, htleft, htinv⟩ := exists_lipschitz_left_pair f (mapReal φ g)
    let δ := bchLatticeSeparationRadius t (Fintype.card κ) HF l
    have hδ : 0 < δ := bchLatticeSeparationRadius_pos _ _ _ _
    let a : ℝ := 4 * (Ct : ℝ) ^ 2 * (Fintype.card κ + 1)
    have ha : 0 < a := by dsimp [a]; positivity
    let r : ℝ := min 1 (δ / a)
    have hr : 0 < r := lt_min (by norm_num) (div_pos hδ ha)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrs : 4 * (Ct : ℝ) ^ 2 * (Fintype.card κ + 1) * r ≤ δ := by
      change a * r ≤ δ
      calc
        _ ≤ a * (δ / a) := mul_le_mul_of_nonneg_left (min_le_right _ _) ha.le
        _ = δ := by field_simp
    let q : (ι → ℝ) → (NilpotentLieBCHGroup L s hL ⧸ Γ) := fun v =>
      QuotientGroup.mk (g * (basisHomeomorph e).symm v)
    let p : (κ → ℝ) → (NilpotentLieBCHGroup M t hM ⧸ Λ) := fun v =>
      QuotientGroup.mk (mapReal φ g * (basisHomeomorph f).symm v)
    have hFq (v : ι → ℝ) : F (q v) = p (A v) := by
      change QuotientGroup.mk (mapReal φ (g * (basisHomeomorph e).symm v)) = _
      rw [map_mul, mapReal_basisHomeomorph_symm e f φ]
    have hq0 : q 0 = QuotientGroup.mk g := by
      have hz : (basisHomeomorph (hnil := hL) e).symm 0 = 1 := by
        apply (basisHomeomorph e).injective
        simp only [Homeomorph.apply_symm_apply, basisHomeomorph_apply, coord_one, map_zero]
      simp only [q, hz, mul_one]
    have hqopen : IsOpenMap q := by
      exact QuotientGroup.isOpenMap_coe.comp
        ((Homeomorph.mulLeft g).isOpenMap.comp (basisHomeomorph e).symm.isOpenMap)
    let V : Set (ι → ℝ) := {v | (∀ i, |v i| < 1) ∧ ∀ k, |A v k| < r}
    have hV : IsOpen V := by
      apply IsOpen.inter
      · change IsOpen {v : ι → ℝ | ∀ i, |v i| < (1 : ℝ)}
        rw [Set.setOf_forall]
        exact isOpen_iInter_of_finite
          (fun i : ι => isOpen_lt (continuous_apply i).abs continuous_const)
      · change IsOpen {v : ι → ℝ | ∀ k, |A v k| < r}
        rw [Set.setOf_forall]
        exact isOpen_iInter_of_finite
          (fun k : κ => isOpen_lt ((continuous_apply k).comp A.continuous).abs continuous_const)
    have hV0 : (0 : ι → ℝ) ∈ V := by
      constructor
      · intro i; simp
      · intro k; simpa only [map_zero, Pi.zero_apply, abs_zero] using hr
    let Csrc : ℝ≥0 := Cs * bchBoxMetricConstant s (Fintype.card ι) HE 1
    have hqLip : LipschitzOnWith Csrc q {v | ∀ i, |v i| ≤ 1} := by
      simpa only [one_mul, Function.comp_def, q, Csrc, NNReal.coe_one] using
        (quotientMetricSpace_lipschitz_mk e Γ hΓclosed).comp_lipschitzOnWith
          (hsleft.comp_lipschitzOnWith (lipschitzOn_basisHomeomorph_symm_box
            e ce he hce 1 le_rfl))
    let Ctar : ℝ≥0 := bchInverseBoxConstant t (Fintype.card κ) HF 1 * Ct
    have hpbound (v w : κ → ℝ) (hv : ∀ k, |v k| ≤ r) (hw : ∀ k, |w k| ≤ r) :
        dist v w ≤ Ctar * dist (p v) (p w) := by
      simpa only [NNReal.coe_mul, Ctar, p] using
        (quotient_chart_metric_bounds f cf hf hcf Λ hΛclosed l hl hgrid
          Ct hCt (mapReal φ g) htleft htinv r hr.le hr1 hrs v w hv hw).2
    refine ⟨Csrc * (‖B‖₊ * Ctar), ?_⟩
    change ∃ U ∈ 𝓝 (QuotientGroup.mk g), _
    rw [← hq0]
    apply local_lower_of_open_parameterization q F hqopen hV hV0
    intro v hv w hw
    have hs := hqLip.dist_le_mul v (fun i => (hv.1 i).le) w (fun i => (hw.1 i).le)
    have ha := hAanti.le_mul_dist v w
    have ht := hpbound (A v) (A w) (fun k => (hv.2 k).le) (fun k => (hw.2 k).le)
    rw [hFq, hFq]
    calc
      _ ≤ Csrc * dist v w := hs
      _ ≤ Csrc * (‖B‖₊ * dist (A v) (A w)) :=
        mul_le_mul_of_nonneg_left ha Csrc.coe_nonneg
      _ ≤ Csrc * (‖B‖₊ * (Ctar * dist (p (A v)) (p (A w)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ht (NNReal.coe_nonneg _)) Csrc.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul]; ring

end MetricEmbedding

end Hindman168.OriginalFiberMetric
