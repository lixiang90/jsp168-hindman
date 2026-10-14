import Hindman168.RoughCofinalSubsequences

/-! Actual cofinal sieve-width sequences may repeat or oscillate. A frequent
failure has a subsequence strictly increasing in BOTH its original indices
and its actual widths. This closes a real quantifier gap, not a monotonicity
assumption on the manuscript's original sequence. -/
namespace Hindman168
open Filter
open scoped Classical

theorem rough_cofinal_frequent_strict_subsequence (width : ℕ → ℕ)
    (hwidth : Tendsto width atTop atTop) (P : ℕ → Prop) (hP : ∃ᶠ n in atTop, P n) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (width ∘ f) ∧ ∀ n, P (f n) := by
  have hData (n₀ w₀ : ℕ) : ∃ n : ℕ, n₀ ≤ n ∧ w₀ ≤ width n ∧ P n := by
    obtain ⟨n,hpn,hn,hw⟩ := (hP.and_eventually
      ((eventually_ge_atTop n₀).and (hwidth.eventually (eventually_ge_atTop w₀)))).exists
    exact ⟨n,hn,hw,hpn⟩
  choose next hindex hactual hgood using hData
  let f : ℕ → ℕ := fun n => Nat.rec (next 0 0)
    (fun _ k => next (k+1) (width k+1)) n
  have hf : StrictMono f := strictMono_nat_of_lt_succ (fun n => by
    change f n < next (f n+1) (width (f n)+1)
    exact (Nat.lt_succ_self _).trans_le (hindex _ _))
  have hwf : StrictMono (width ∘ f) := strictMono_nat_of_lt_succ (fun n => by
    change width (f n) < width (next (f n+1) (width (f n)+1))
    exact (Nat.lt_succ_self _).trans_le (hactual _ _))
  have hp : ∀ n, P (f n) := by
    intro n
    cases n <;> exact hgood _ _
  exact ⟨f,hf,hwf,hp⟩

theorem rough_cofinal_eventually_from_strict_subsequences (width : ℕ → ℕ)
    (hwidth : Tendsto width atTop atTop) (P : ℕ → Prop)
    (hsub : ∀ f : ℕ → ℕ, StrictMono f → StrictMono (width ∘ f) → ∀ᶠ n in atTop, P (f n)) :
    ∀ᶠ n in atTop, P n := by
  by_contra hn
  have hbad : ∃ᶠ n in atTop, ¬P n := by
    change ¬∀ᶠ n in atTop, ¬¬P n
    simpa only [not_not] using hn
  obtain ⟨f,hf,hwf,hp⟩ := rough_cofinal_frequent_strict_subsequence width hwidth (fun n => ¬P n) hbad
  obtain ⟨n,hgood,hfail⟩ := ((hsub f hf hwf).and (Eventually.of_forall hp)).exists
  exact hfail hgood

theorem rough_cofinal_tendsto_from_strict_subsequences {α : Type*} {l : Filter α}
    (width : ℕ → ℕ) (hwidth : Tendsto width atTop atTop) (f : ℕ → α)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ → StrictMono (width ∘ φ) → Tendsto (f ∘ φ) atTop l) :
    Tendsto f atTop l := by
  apply tendsto_def.mpr
  intro S hS
  apply rough_cofinal_eventually_from_strict_subsequences width hwidth (fun n => f n ∈ S)
  intro φ hφ hwφ
  exact (hsub φ hφ hwφ).eventually hS

end Hindman168
