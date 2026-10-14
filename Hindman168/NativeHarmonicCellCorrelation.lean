import Hindman168.NativeCellCorrelationTransfer
import Hindman168.CompleteCellBoundedHarmonicError

namespace Hindman168
open scoped BigOperators Classical
open NNReal
universe u

/-- Transport the original native period correlator to the actual
conditional harmonic cell law, with the explicit uniform B*Mq/X error. -/
theorem native_complete_cell_harmonic_correlation_transfer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (X W : ℕ) (k : ℤ) (M q K : ℕ) [NeZero q]
    (hX : 0 < X) (hM : 0 < M) (hK : 0 < K) (hWM : W ∣ M)
    (r : Fin M) (hr : r.val.Coprime W) (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (f : ℤ → ℝ) (obs : C(D.G ⧸ D.Γ, ℂ)) (g x : D.G) (B : ℝ) (Lip : ℝ≥0) (δ : ℝ),
      (∀ y, |f y| ≤ 1) → 0 ≤ B → (∀ z, ‖obs z‖ ≤ B) → LipschitzWith Lip obs →
      δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
        (f (k * (M * q : ℕ) + r.val + (M : ℤ) * (n.val : ZMod q).val) : ℂ) *
          obs (g ^ (n.val : ℤ) * x))‖ →
      ∃ (j : Fin K) (x' : D.G) (η : ℂ) (obs' : C(D.G ⧸ D.Γ, ℝ)),
        x' = g ^ (-(k * q)) * (g ^ ((j.val * q : ℕ) : ℤ) * x) ∧
        ‖η‖ = 1 ∧ obs' = phaseRealObservable η obs ∧
        (∀ z, |obs' z| ≤ B) ∧ LipschitzWith Lip obs' ∧
        δ - B * ((M * q : ℕ) / (X : ℝ)) ≤
          (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
            integerMass X W y * (f y * obs' (pieceLinearOrbit D.Γ M
              (fun _ : Unit => g) (fun _ => x') () y))) /
            (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro f obs g x B Lip δ hf hB hb hl hδ
  obtain ⟨j, x', η, obs', hx', hη, he, hb', hl', hc⟩ :=
    native_complete_cell_correlation_transfer D k M q K hM hK r f obs g x B Lip δ hb hl hδ
  refine ⟨j, x', η, obs', hx', hη, he, hb', hl', ?_⟩
  let F := fun y : ℤ => f y * obs' (pieceLinearOrbit D.Γ M
    (fun _ : Unit => g) (fun _ => x') () y)
  have hF (y : ℤ) : |F y| ≤ B := by
    rw [show F y = f y * obs' (pieceLinearOrbit D.Γ M
      (fun _ : Unit => g) (fun _ => x') () y) from rfl, abs_mul]
    exact (mul_le_mul_of_nonneg_right (hf y) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hb' _)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have ha : (X : ℝ) ≤ (k : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have herr := completeResidueCell_integerMass_bounded_error X W k M q hM hq hWM r hr hZ
    hlo hhi (hx.trans_le ha) F B hB hF
  have hcost : B * ((M * q : ℕ) / ((k : ℝ) * (M * q : ℕ))) ≤
      B * ((M * q : ℕ) / (X : ℝ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hx ha) hB
  have hlower := (abs_le.mp (herr.trans hcost)).1
  change δ ≤ finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t)) at hc
  change δ - B * ((M * q : ℕ) / (X : ℝ)) ≤
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y * F y) /
      (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y)
  linarith only [hlower, hc]

end Hindman168
