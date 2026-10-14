import Hindman168.CyclicIntervalPositiveNormTransfer
import Hindman168.NativePeriodCellRecipeSynthesis

namespace Hindman168
open NNReal
open scoped Classical
universe u v

/-- A fixed finite-list interval inverse conclusion, applied only to
periodic extensions on the actual signed-parameter interval cube domain,
gives one fixed period count for all original integer cells. This is an
implication from the displayed inverse input, not its existence proof. -/
theorem native_interval_inverse_to_cell_correlators {s : ℕ} {ι : Type v}
    (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0)
    (d : ℕ) (hd : 0 < d) (η γ : ℝ) (hη : 0 < η)
    (hinterval : ∀ (q : ℕ) [NeZero q] (K : ℕ) (v : ZMod q → ℝ),
      (∀ z, |v z| ≤ 1) →
      η / 2 ≤ integerIntervalPeriodicGowersValue q d (K * q) v →
      ∃ i : ι,
        letI := (D i).metric
        letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
          (D i).metric.toUniformSpace.toTopologicalSpace
        ∃ (obs : C((D i).G ⧸ (D i).Γ, ℂ)) (g x : (D i).G),
          (∀ z, ‖obs z‖ ≤ 1) ∧ LipschitzWith (Lip i) obs ∧
          γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
            (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖) :
    ∃ K : ℕ, 0 < K ∧ ∀ (M q : ℕ) [NeZero q] (k : ℤ) (r : Fin M) (f : ℤ → ℝ),
      (∀ y, |f y| ≤ 1) →
      η ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d
        (fun z => f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val)) →
      ∃ i, HasNativePeriodCellCorrelator (D i) M q K k r f γ (Lip i) := by
  obtain ⟨K, hK, htransfer⟩ := cyclic_positive_norm_interval_transfer d hd η hη
  refine ⟨K, (Nat.succ_pos d).trans_le hK, ?_⟩
  intro M q _ k r f hf hn
  let v := fun z : ZMod q => f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val)
  have hunit (z : ZMod q) : |v z| ≤ 1 := hf _
  have hnorm := (htransfer q v hunit hn).2
  obtain ⟨i, hi⟩ := hinterval q K v hunit hnorm
  exact ⟨i, hi⟩

end Hindman168
