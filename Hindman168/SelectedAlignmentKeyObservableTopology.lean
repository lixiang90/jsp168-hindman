import Hindman168.AlignmentJointObservableCompactnessNative

/-! The native recipe metric and the original quotient topology are equal,
but not definitionally equal. These transports preserve the actual observer
function, hence preserve its original bounds, Lipschitz constants and uniform
limits exactly. No new metric or model is introduced. -/
namespace Hindman168
open Filter NNReal
open scoped Topology
universe u

noncomputable def selectedAlignmentQuotientObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance) :
    C(D.G ⧸ D.Γ, ℝ) :=
  ⟨@ContinuousMap.toFun _ _ D.metric.toUniformSpace.toTopologicalSpace _ f,
    Eq.mp (congrArg (fun t => @Continuous (D.G ⧸ D.Γ) ℝ t inferInstance
      (@ContinuousMap.toFun _ _ D.metric.toUniformSpace.toTopologicalSpace _ f))
      (nativeNilmanifold_metric_topology D).symm)
      (@ContinuousMap.continuous_toFun _ _ D.metric.toUniformSpace.toTopologicalSpace _ f)⟩

noncomputable def selectedAlignmentMetricObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : C(D.G ⧸ D.Γ, ℝ)) :
    @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance :=
  @ContinuousMap.mk _ _ D.metric.toUniformSpace.toTopologicalSpace _
    (@ContinuousMap.toFun _ _ (QuotientGroup.instTopologicalSpace D.Γ) _ f)
    (Eq.mp (congrArg (fun t => @Continuous (D.G ⧸ D.Γ) ℝ t inferInstance
      (@ContinuousMap.toFun _ _ (QuotientGroup.instTopologicalSpace D.Γ) _ f))
      (nativeNilmanifold_metric_topology D))
      (@ContinuousMap.continuous_toFun _ _ (QuotientGroup.instTopologicalSpace D.Γ) _ f))

@[simp] theorem selected_alignment_quotient_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance)
    (x : D.G ⧸ D.Γ) : selectedAlignmentQuotientObservable D f x = f x := rfl

@[simp] theorem selected_alignment_metric_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : C(D.G ⧸ D.Γ, ℝ)) (x : D.G ⧸ D.Γ) : selectedAlignmentMetricObservable D f x = f x := rfl

@[simp] theorem selected_alignment_metric_quotient_observable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance) :
    selectedAlignmentMetricObservable D (selectedAlignmentQuotientObservable D f) = f := rfl

@[simp] theorem selected_alignment_quotient_metric_observable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : C(D.G ⧸ D.Γ, ℝ)) :
    selectedAlignmentQuotientObservable D (selectedAlignmentMetricObservable D f) = f := rfl

theorem selected_alignment_quotient_observable_bound_iff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance) (B : ℝ) :
    (∀ x, |selectedAlignmentQuotientObservable D f x| ≤ B) ↔ (∀ x, |f x| ≤ B) := Iff.rfl

theorem selected_alignment_metric_observable_bound_iff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : C(D.G ⧸ D.Γ, ℝ)) (B : ℝ) :
    (∀ x, |selectedAlignmentMetricObservable D f x| ≤ B) ↔ (∀ x, |f x| ≤ B) := Iff.rfl

theorem selected_alignment_quotient_observable_lipschitz_iff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance)
    (Lip : ℝ≥0) :
    letI := D.metric
    LipschitzWith Lip (fun x => selectedAlignmentQuotientObservable D f x) ↔
      LipschitzWith Lip (fun x => f x) := Iff.rfl

theorem selected_alignment_metric_observable_lipschitz_iff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : C(D.G ⧸ D.Γ, ℝ)) (Lip : ℝ≥0) :
    letI := D.metric
    LipschitzWith Lip (fun x => selectedAlignmentMetricObservable D f x) ↔
      LipschitzWith Lip (fun x => f x) := Iff.rfl

/-- A metric-topology Ascoli limit has the same function and is continuous
for the original quotient topology after this exact transport. -/
theorem selected_alignment_quotient_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (f : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance) :
    Continuous (fun x => selectedAlignmentQuotientObservable D f x) :=
  (selectedAlignmentQuotientObservable D f).continuous

theorem selected_alignment_quotient_observable_uniform_limit_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s)
    (f : ℕ → @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance)
    (g : @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance) :
    TendstoUniformly (fun m x => selectedAlignmentQuotientObservable D (f m) x)
      (fun x => selectedAlignmentQuotientObservable D g x) atTop ↔
    TendstoUniformly (fun m x => f m x) (fun x => g x) atTop := Iff.rfl

theorem selected_alignment_metric_observable_uniform_limit_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (f : ℕ → C(D.G ⧸ D.Γ, ℝ)) (g : C(D.G ⧸ D.Γ, ℝ)) :
    TendstoUniformly (fun m x => selectedAlignmentMetricObservable D (f m) x)
      (fun x => selectedAlignmentMetricObservable D g x) atTop ↔
    TendstoUniformly (fun m x => f m x) (fun x => g x) atTop := Iff.rfl

/-- Original native recipes and their integer values are unchanged. -/
theorem selected_alignment_quotient_observable_piecewise {s N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (obs : ℕ → (ℤ × ℤ) → @ContinuousMap (D.G ⧸ D.Γ) ℝ D.metric.toUniformSpace.toTopologicalSpace inferInstance)
    (g a : ℕ → (ℤ × ℤ) → D.G) :
    piecewiseLinearNilsequence D.Γ F gap (fun w p => selectedAlignmentQuotientObservable D (obs w p)) g a =
    (letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
     piecewiseLinearNilsequence D.Γ F gap obs g a) := rfl

end Hindman168
