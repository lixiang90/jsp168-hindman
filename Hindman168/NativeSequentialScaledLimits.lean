import Hindman168.NativeSequentialFiniteDescent
import Mathlib.Topology.Sequences

/-! ONE further subsequence gives limits for every actual bounded scaled
smooth coefficient in the finite factor list. The all-character limits
survive every strictly increasing subsequence. No pointwise choice of
different subsequences is used. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem finite_bounded_real_joint_subsequence {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (C : ι → ℝ) (h : ∀ n i, |x n i| ≤ C i) :
    ∃ c : ι → ℝ, ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i,
      Tendsto (fun n => x (f n) i) atTop (𝓝 (c i)) := by
  have hx : ∀ n, x n ∈ Icc (fun i => -C i) C := by
    intro n
    exact ⟨fun i => (abs_le.mp (h n i)).1, fun i => (abs_le.mp (h n i)).2⟩
  have hc : IsCompact (Icc (fun i => -C i) C) := isCompact_Icc
  obtain ⟨c,_,f,hf,hlim⟩ := hc.tendsto_subseq hx
  exact ⟨c,f,hf,fun i => tendsto_pi_nhds.mp hlim i⟩

theorem native_sequential_scaled_coefficients_joint_limits {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ℓ : ℕ) (L : ℕ → ℝ) (hpos : ∀ n, 0 < L n)
    (as : List (NativeSequentialBinomialFactor D))
    (hadm : ∀ a ∈ as, NativeSequentialBinomialFactorAdmissible D ℓ L a) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ a ∈ as, ∃ c : ℝ,
      Tendsto (fun n => (L (f n))^a.order * a.realCoefficient (f n)) atTop (𝓝 c) := by
  classical
  have hdata (i : Fin as.length) : ∃ C : ℝ, 1 ≤ C ∧
      ∀ n, (L n)^(as.get i).order * |(as.get i).realCoefficient n| ≤ C :=
    (hadm (as.get i) (List.get_mem as i)).2.2.2
  choose C _ hbound using hdata
  let x (n : ℕ) (i : Fin as.length) : ℝ := (L n)^(as.get i).order * (as.get i).realCoefficient n
  have hxb : ∀ n i, |x n i| ≤ C i := by
    intro n i
    dsimp only [x]
    rw [abs_mul, abs_of_pos (pow_pos (hpos n) _)]
    exact hbound i n
  obtain ⟨c,f,hf,hlim⟩ := finite_bounded_real_joint_subsequence x C hxb
  refine ⟨f,hf,?_⟩
  apply (List.forall_mem_iff_get (l := as) (p := fun a => ∃ c : ℝ,
    Tendsto (fun n => (L (f n))^a.order * a.realCoefficient (f n)) atTop (𝓝 c))).mpr
  intro i
  exact ⟨c i,hlim i⟩

theorem native_subgroup_sequential_irrational_subsequence {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (h : NativeSubgroupSequentialIrrational D F L p) (f : ℕ → ℕ) (hf : StrictMono f) :
    NativeSubgroupSequentialIrrational D F (L ∘ f) (p ∘ f) := by
  intro j hj hjTop phi hphi
  exact (h j hj hjTop phi hphi).comp hf.tendsto_atTop

end Hindman168
