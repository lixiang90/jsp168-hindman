import Hindman168.ProductSamplingAsymptotics
import Hindman168.GlobalChainLaw
import Hindman168.NormedExpectation
import Mathlib.Order.Filter.Finite

/-!
# Fixed finite joint sampling laws at every inverse-power scale

Only the number of coordinates is fixed. Their cutoff values and errors
may vary with the asymptotic parameter. Small L1 error itself bounds each
unnormalized positive comparison mass by two eventually; tensor factors
are retained until this bound is proved.
-/

namespace Hindman168.FiniteMass

theorem total_distance_le {β : Type*} (μ ν : Mass β) :
    |total μ - total ν| ≤ distance μ ν := by
  rw [← total_sub]
  exact Finset.abs_sum_le_sum_abs _ _

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped Topology BigOperators

theorem RapidlySmall.finset_sum {α ι : Type*} {l : Filter α}
    {V : α → ℝ} (S : Finset ι) (e : ι → α → ℝ)
    (he : ∀ i ∈ S, RapidlySmall l V (e i)) :
    RapidlySmall l V (fun w => ∑ i ∈ S, e i w) :=
  fun C => IsLittleO.sum (fun i hi => he i hi C)

theorem RapidlySmall.eventually_abs_le_one {α : Type*} {l : Filter α}
    {V e : α → ℝ} (he : RapidlySmall l V e) : ∀ᶠ w in l, |e w| ≤ 1 := by
  simpa only [pow_zero, inv_one, norm_one, Real.norm_eq_abs, mul_one] using
    (he 0).bound (by norm_num : (0 : ℝ) < 1)

theorem finite_tensor_rapid {α β : Type*} {l : Filter α} {m : ℕ}
    {V : α → ℝ} {μ ν : α → Fin m → FiniteMass.Mass β}
    (hμ : ∀ᶠ w in l, ∀ i, (∀ b, 0 ≤ μ w i b) ∧ FiniteMass.total (μ w i) = 1)
    (hν : ∀ᶠ w in l, ∀ i b, 0 ≤ ν w i b)
    (hd : ∀ i, RapidlySmall l V (fun w => FiniteMass.distance (μ w i) (ν w i))) :
    RapidlySmall l V (fun w =>
      FiniteMass.distance (FiniteMass.tensorList (List.ofFn (μ w)))
        (FiniteMass.tensorList (List.ofFn (ν w)))) := by
  let E : α → ℝ := fun w => ∑ i : Fin m, FiniteMass.distance (μ w i) (ν w i)
  have hE : RapidlySmall l V E :=
    RapidlySmall.finset_sum Finset.univ
      (fun i w => FiniteMass.distance (μ w i) (ν w i)) (fun i _ => hd i)
  have hdsmall : ∀ᶠ w in l, ∀ i, |FiniteMass.distance (μ w i) (ν w i)| ≤ 1 :=
    eventually_all.mpr (fun i => (hd i).eventually_abs_le_one)
  apply (hE.const_mul (∑ j ∈ Finset.range m, (2 : ℝ) ^ j)).of_abs_le
  filter_upwards [hμ, hν, hdsmall] with w hμw hνw hdw
  have hm (i : Fin m) : FiniteMass.total (ν w i) ≤ 2 := by
    have ht := FiniteMass.total_distance_le (μ w i) (ν w i)
    rw [(hμw i).2] at ht
    have hb := (hdw i)
    rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _)] at hb
    have hl := (abs_le.mp ht).1
    linarith
  have he (i : Fin m) : FiniteMass.distance (μ w i) (ν w i) ≤ E w :=
    Finset.single_le_sum (fun j _ => FiniteMass.distance_nonneg (μ w j) (ν w j)) (Finset.mem_univ i)
  have h := FiniteMass.tensorList_distance_uniform
    (List.ofFn (fun i => (μ w i, ν w i))) (E := E w) (M := 2) (by norm_num)
  have hp : ∀ p ∈ List.ofFn (fun i => (μ w i, ν w i)),
      (∀ b, 0 ≤ p.1 b) ∧ FiniteMass.total p.1 = 1 ∧ (∀ b, 0 ≤ p.2 b) ∧
        FiniteMass.total p.2 ≤ 2 ∧ FiniteMass.distance p.1 p.2 ≤ E w := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨(hμw i).1, (hμw i).2, hνw i, hm i, he i⟩
  have hbound : FiniteMass.distance (FiniteMass.tensorList (List.ofFn (μ w)))
      (FiniteMass.tensorList (List.ofFn (ν w))) ≤
        (∑ j ∈ Finset.range m, (2 : ℝ) ^ j) * E w := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn, mul_comm] using h hp
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _)]
  exact hbound.trans (le_abs_self _)

theorem joint_product_law_rapid {α : Type*} {l : Filter α} {m : ℕ}
    {W V : α → ℕ} {b : α → Fin m → BlockCutoffs}
    (hD : ∀ i, PowerDominates l (fun w => Real.log (b w i).pivotCutoff)
      (fun w => (samplingSize (W w) (tailBound (b w i).tailCutoffs) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (ht : ∀ᶠ w in l, ∀ i, ValidCutoffs (b w i).tailCutoffs (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (jointOriginal (W w) (List.ofFn (b w)))
        (jointComparison (W w) (List.ofFn (b w)))) := by
  have hv : ∀ᶠ w in l, ∀ i, ValidBlockCutoffs (W w) (b w i) := by
    apply eventually_all.mpr
    intro i
    filter_upwards [sampling_eventually_geometry (powerDominates_log_to_cutoff (hD i)), ht]
      with w hw htw
    exact ⟨htw i, by omega, sampling_denominator_pos hw.1 hw.2.1, hw.2.2⟩
  have hμ : ∀ᶠ w in l, ∀ i,
      (∀ n, 0 ≤ blockOriginal (W w) (b w i) n) ∧
        FiniteMass.total (blockOriginal (W w) (b w i)) = 1 := by
    filter_upwards [hW, hv] with w hWw hvw i
    exact ⟨blockOriginal_nonneg (b w i) hWw (hvw i), blockOriginal_total (b w i) hWw (hvw i)⟩
  have hν : ∀ᶠ w in l, ∀ i n, 0 ≤ blockComparison (W w) (b w i) n := by
    filter_upwards [hW, hv] with w hWw hvw i n
    exact blockComparison_nonneg (b w i) hWw (hvw i) n
  have hd (i : Fin m) : RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (blockOriginal (W w) (b w i)) (blockComparison (W w) (b w i))) :=
    block_product_law_rapid (hD i) hV hW (ht.mono (fun _ hw => hw i))
  simpa only [jointOriginal, jointComparison, List.map_ofFn, Function.comp_def] using
    finite_tensor_rapid hμ hν hd

theorem integer_joint_product_law_rapid {α : Type*} {l : Filter α} {m : ℕ}
    {W V : α → ℕ} {b : α → Fin m → BlockCutoffs}
    (hD : ∀ i, PowerDominates l (fun w => Real.log (b w i).pivotCutoff)
      (fun w => (samplingSize (W w) (tailBound (b w i).tailCutoffs) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (ht : ∀ᶠ w in l, ∀ i, ValidCutoffs (b w i).tailCutoffs (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (jointIntegerOriginal (W w) (List.ofFn (b w)))
        (jointIntegerComparison (W w) (List.ofFn (b w)))) := by
  simpa only [jointIntegerOriginal, jointIntegerComparison,
    FiniteMass.distance_push_injective
      (f := fun xs : List ℕ => xs.map (fun n : ℕ => (n : ℤ))) list_natCast_injective] using
    joint_product_law_rapid hD hV hW ht

theorem global_chain_joint_rapid {α : Type*} {l : Filter α} {m N : ℕ}
    (C : Chain m) {X : α → ℕ → ℕ} {W V : α → ℕ}
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hD : ∀ i, PowerDominates l (fun w => Real.log (C.cutoffs (X w) i).pivotCutoff)
      (fun w => (samplingSize (W w) (tailBound (C.cutoffs (X w) i).tailCutoffs) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (ht : ∀ᶠ w in l, ∀ i, ValidCutoffs (C.cutoffs (X w) i).tailCutoffs (W w))
    (hZ : ∀ᶠ w in l, ∀ j : Fin N, 0 < harmonicNormalizer (X w j) (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance
        ((globalRawMass (X w) (W w) N).mapDomain (fun x => List.ofFn (C.sampleProducts hN x)))
        (jointComparison (W w) (List.ofFn (C.cutoffs (X w))))) := by
  apply (joint_product_law_rapid hD hV hW ht).of_abs_le
  filter_upwards [hZ] with w hZw
  rw [global_chain_joint_mass C (X w) (W w) hN hZw]

end Hindman168
