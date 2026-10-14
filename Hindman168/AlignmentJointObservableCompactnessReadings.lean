import Hindman168.AlignmentJointObservableCompactnessNative
import Hindman168.PositivePrincipalSumNativeReadings
import Hindman168.AlignmentJointPointMixture

/-! Uniformly frozen observations are evaluated on the actual original joint
integer orbit. The integer exponent includes its original residue correction;
the observers and every joint source datum use the same further subsequence. -/
namespace Hindman168
open Filter MeasureTheory NNReal
open scoped Topology Manifold ContDiff
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

/-- One further subsequence works for every component and ALL integer slots
on the same full joint quotient, including unbounded slots. -/
theorem alignment_native_joint_frozen_observables :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
      fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
      (B : ι → ℝ) (Lip : ι → ℝ≥0),
      (∀ ν w p z, |obs ν w p z| ≤ B ν) →
      (∀ ν w p, LipschitzWith (Lip ν) (obs ν w p)) →
      ∀ (width selected : ℕ → ℕ) (label : ℕ → ∀ ν, ℤ × ℤ),
      ∃ limit : ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ),
        ∃ further : ℕ → ℕ, StrictMono further ∧
          (∀ ν, TendstoUniformly
            (fun m => obs ν (width (selected (further m))) (label (selected (further m)) ν))
            (limit ν) atTop) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ ν slots z,
            |obs ν (width (selected (further m))) (label (selected (further m)) ν)
                (alignmentJointNativeCosetEvaluation D n v hv ν slots z) -
              limit ν (alignmentJointNativeCosetEvaluation D n v hv ν slots z)| < ε := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
    fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs B Lip hB hLip width selected label
  obtain ⟨limit, further, hfurther, hconv⟩ :=
    alignment_native_frozen_observables_compactness D obs B Lip hB hLip width selected label
  refine ⟨limit, further, hfurther, hconv, ?_⟩
  intro ε hε
  have he := alignment_uniform_observers_finite_joint_readings
    (fun m ν => obs ν (width (selected (further m))) (label (selected (further m)) ν))
    (fun ν => limit ν) hconv
    (fun ν _ slots z => alignmentJointNativeCosetEvaluation D n v hv ν slots z)
    Finset.univ ε hε
  simpa only [Finset.mem_univ, forall_const] using he

/-- The uniform estimate controls the original integer reading, rather than a
surrogate marginal orbit. The actual integer-argument identity is proved by
the existing original-source theorem. -/
theorem alignment_native_original_integer_readings_limit
    (obs : ℕ → ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (limit : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (hconv : ∀ ν, TendstoUniformly (fun m => obs m ν) (limit ν) atTop)
    (F : MasterParameterFamily) (q₀ : ℕ) (targets : ι → Finset (Fin N))
    (width : ℕ → ℕ) (y : ℕ → Fin N → ℕ) (p : ℕ → ℤ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _m : ℕ, ∀ ν, (D ν).G) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ ν slots ell,
      |obs m ν ((g m ν ^
          (alignmentIntegerArrayArgument (y m) (F.modulus (width m))
            (fun e => alignmentPairResidue q₀ (width m) (F.modulus (width m)) e (y m))
            (fun e => alignmentPairProgression q₀ (width m) (F.modulus (width m)) e (y m))
            (targets ν) (p m + (F.modulus (width m) : ℤ) * ell) (shift m ν) slots /
              (F.modulus (width m) : ℤ)) * a m ν : (D ν).G ⧸ (D ν).Γ)) -
        limit ν (alignmentJointNativeCosetEvaluation D n v hv ν slots
          (QuotientGroup.mk (alignmentOriginalJointPointOrbit D n v hv F q₀ (width m)
            targets (y m) (p m) (shift m) (g m) (a m) ell)))| < ε := by
  have he := alignment_uniform_observers_finite_joint_readings obs limit hconv
    (fun ν _ slots z => alignmentJointNativeCosetEvaluation D n v hv ν slots z)
    Finset.univ ε hε
  filter_upwards [he] with m hm
  intro ν slots ell
  rw [← principal_native_joint_reading_integer_argument D n v hv F q₀ (width m)
    targets (y m) (p m) (shift m) (g m) (a m) ell ν slots (obs m ν)]
  exact hm ν (Finset.mem_univ ν) slots _

end Hindman168
