import Hindman168.RoughPartitionWeightComparison
import Hindman168.PowerGrowth

namespace Hindman168
open Filter
open scoped Topology

theorem rough_linear_scale_strict {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w)
    (hZ : ∀ᶠ w in l, 0 ≤ Z w) (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ w in l, L*S w < Z w := by
  have hs0 : ∀ᶠ w in l, 0 ≤ S w := hS.mono (fun _ h => by linarith)
  filter_upwards [hS, hg.eventually_bound hZ hs0 1 (by positivity : 0 < L+1)] with w hs hh
  simp only [pow_one] at hh
  nlinarith

theorem rough_partition_scale_thresholds {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w)
    (hZ : ∀ᶠ w in l, 0 ≤ Z w) (N K d : ℕ) (hN : 0 < N) (hK : 0 < K)
    (c M ε : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ w in l, 0 < Z w ∧ ∀ t : ℕ, (t : ℝ) ≤ 2*S w →
      2*(N : ℝ) ≤ c*Z w ∧
      2*(N : ℝ)*(t*K) ≤ c*Z w ∧
      2*(t : ℝ) ≤ c*Z w ∧
      M * (((N^d*K^d : ℕ) : ℝ)*d*(5*(t : ℝ)/(c*Z w))) < ε := by
  let Q : ℝ := ((N^d*K^d : ℕ) : ℝ)
  have hQ : 0 ≤ Q := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hlarge := rough_linear_scale_strict hg hS hZ
    ((4*N*K+2*N+4+10*M*Q*d/ε)/c) (by positivity)
  filter_upwards [hS, hlarge] with w hs hh
  have hs0 : 0 ≤ S w := by linarith
  have hh' : (4*N*K+2*N+4+10*M*Q*d/ε)*S w < c*Z w := by
    have hh2 := mul_lt_mul_of_pos_left hh hc
    have heq : c*((4*N*K+2*N+4+10*M*Q*d/ε)/c*S w) =
        (4*N*K+2*N+4+10*M*Q*d/ε)*S w := by field_simp
    rwa [heq] at hh2
  have hterm : 0 ≤ 10*M*Q*d/ε := by positivity
  have hbase : 4*N*K+2*N+4+10*M*Q*d/ε ≥ 4 := by nlinarith
  have hcz : 0 < c*Z w := by nlinarith
  have hz : 0 < Z w := (pos_of_mul_pos_right hcz hc.le)
  refine ⟨hz, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hnk : 0 ≤ (N : ℝ)*K := by positivity
  have hmul := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2*N*K)
  have hnk1 : (1 : ℝ) ≤ (N : ℝ)*K := by nlinarith
  have h1 : 2*(N : ℝ) ≤ c*Z w := by nlinarith
  have h2 : 2*(N : ℝ)*(t*K) ≤ c*Z w := by nlinarith
  have h3 : 2*(t : ℝ) ≤ c*Z w := by nlinarith
  refine ⟨h1, h2, h3, ?_⟩
  change M*(Q*d*(5*(t : ℝ)/(c*Z w))) < ε
  have he : (10*M*Q*d/ε)*S w < c*Z w := by nlinarith
  have he' : 10*M*Q*d*S w < ε*(c*Z w) := by
    have hm := mul_lt_mul_of_pos_left he hε
    have heq : ε*((10*M*Q*d/ε)*S w) = 10*M*Q*d*S w := by field_simp
    rwa [heq] at hm
  have ht' := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 5*M*Q*d)
  have hid : M*(Q*d*(5*(t : ℝ)/(c*Z w))) = (5*M*Q*d*t)/(c*Z w) := by ring
  rw [hid]
  apply (div_lt_iff₀ hcz).mpr
  nlinarith

end Hindman168
