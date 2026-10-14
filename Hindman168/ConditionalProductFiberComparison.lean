import Hindman168.IndependentFiberEvents
import Hindman168.FinitePivotCoordinates
import Hindman168.FiniteSetConditionDomination

/-! The source conditional rough-step probability argument: exact Fubini
under the ORIGINAL product laws, support-restricted uniform fibers, a finite
union, and a fixed domination constant. Conditioning is not independence. -/
namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

theorem rough_uniform_finset_event_eq_fraction {α : Type*} (S : Finset α) (E : α → Prop) :
    event (uniformFinsetMass S) E = ((S.filter E).card : ℝ)/(S.card : ℝ) := by
  have hsupport : (uniformFinsetMass S).support ⊆ S := flatMass_support S _
  rw [event_eq_sum (uniformFinsetMass S) E hsupport]
  have hsum : (∑ x ∈ S, if E x then uniformFinsetMass S x else 0) =
      ∑ x ∈ S, if E x then (S.card : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [uniformFinsetMass,flatMass_apply,if_pos hx]
  rw [hsum,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

theorem rough_uniform_finset_count_bound_event_lt {α : Type*} (S : Finset α) (E : α → Prop)
    (δ : ℝ) (hδ : 0 < δ) (hcount : ((S.filter E).card : ℝ) < δ*(S.card : ℝ)) :
    event (uniformFinsetMass S) E < δ := by
  have hS : (0 : ℝ) < S.card := by
    have hn : (0 : ℝ) ≤ (S.filter E).card := Nat.cast_nonneg _
    nlinarith
  rw [rough_uniform_finset_event_eq_fraction]
  exact (div_lt_iff₀ hS).mpr (by simpa only [mul_comm] using hcount)

theorem rough_pi_mass_pivot_fiber_le {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (i : ι) (E : (ι → α) → Prop)
    (hμ : ∀ j x, 0 ≤ μ j x) (ht : ∀ j, total (μ j)=1) (ε : ℝ)
    (hcap : ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ j.val)).support,
      event (μ i) (fun value => E (insertPivotCoordinate i rest value)) ≤ ε) :
    event (piMass μ) E ≤ ε := by
  let e : (ι → α) ≃ (({j : ι // j ≠ i} → α) × α) := pivotCoordinateEquiv i
  have he := event_map (piMass μ) e (fun p => E (e.symm p))
  rw [piMass_pivotCoordinate μ i] at he
  have heq : event (piMass μ) E =
      event (tensor (piMass (fun j : {j : ι // j ≠ i} => μ j.val)) (μ i))
        (fun p => E (insertPivotCoordinate i p.1 p.2)) := by
    have hcancel : (fun x => E (e.symm (e x)))=E := by
      funext x
      exact congrArg E (e.symm_apply_apply x)
    have hinverse : (fun p => E (e.symm p))=(fun p => E (insertPivotCoordinate i p.1 p.2)) := rfl
    rw [hcancel,hinverse] at he
    exact he.symm
  rw [heq]
  exact event_tensor_fiber_le (piMass (fun j : {j : ι // j ≠ i} => μ j.val)) (μ i)
    (fun p => E (insertPivotCoordinate i p.1 p.2))
    (piMass_nonneg _ (fun j => hμ j.val))
    (piMass_total_one _ (fun j => ht j.val)) hcap

theorem rough_pi_mass_coordinate_union_le {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (E : ι → (ι → α) → Prop)
    (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i)=1) (ε : ι → ℝ)
    (hcap : ∀ i, ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ j.val)).support,
      event (μ i) (fun value => E i (insertPivotCoordinate i rest value)) ≤ ε i) :
    event (piMass μ) (fun x => ∃ i, E i x) ≤ ∑ i, ε i := by
  have heq : (fun x => ∃ i, E i x)=(fun x => ∃ i ∈ (Finset.univ : Finset ι), E i x) := by
    funext x
    simp
  rw [heq]
  apply (event_union_bound (piMass μ) Finset.univ E (piMass_nonneg μ hμ)).trans
  exact Finset.sum_le_sum (fun i _ => rough_pi_mass_pivot_fiber_le μ i (E i) hμ ht (ε i) (hcap i))

theorem rough_dominated_pi_mass_coordinate_union_le {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (ρ : Mass (ι → α)) (E : ι → (ι → α) → Prop)
    (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i)=1)
    (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hdom : ∀ x, ρ x ≤ C₀*piMass μ x)
    (hcap : ∀ i, ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ j.val)).support,
      event (μ i) (fun value => E i (insertPivotCoordinate i rest value)) ≤ ε) :
    event ρ (fun x => ∃ i, E i x) ≤ C₀*(Fintype.card ι : ℝ)*ε := by
  apply (event_pointwise_domination ρ (piMass μ) hdom _).trans
  have hprod := rough_pi_mass_coordinate_union_le μ E hμ ht (fun _ => ε) hcap
  have hsum : (∑ _i : ι, ε)=(Fintype.card ι : ℝ)*ε := by simp
  rw [hsum] at hprod
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hC₀

theorem rough_condition_mass_event_lower_domination {α : Type*}
    (ν : Mass α) (A : α → Prop) (hν : ∀ x, 0 ≤ ν x)
    (a : ℝ) (ha : 0 < a) (hA : a ≤ event ν A) (x : α) :
    conditionMass ν A x ≤ a⁻¹*ν x := by
  rw [conditionMass_apply]
  split_ifs
  · simpa only [div_eq_mul_inv,mul_comm] using div_le_div_of_nonneg_left (hν x) ha hA
  · exact mul_nonneg (inv_nonneg.mpr ha.le) (hν x)

theorem rough_conditioned_pi_mass_coordinate_union_le {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (A : (ι → α) → Prop) (E : ι → (ι → α) → Prop)
    (hμ : ∀ i x, 0 ≤ μ i x) (ht : ∀ i, total (μ i)=1)
    (a ε : ℝ) (ha : 0 < a) (hA : a ≤ event (piMass μ) A)
    (hcap : ∀ i, ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ j.val)).support,
      event (μ i) (fun value => E i (insertPivotCoordinate i rest value)) ≤ ε) :
    event (conditionMass (piMass μ) A) (fun x => ∃ i, E i x) ≤ a⁻¹*(Fintype.card ι : ℝ)*ε :=
  rough_dominated_pi_mass_coordinate_union_le μ _ E hμ ht a⁻¹ ε (inv_nonneg.mpr ha.le)
    (rough_condition_mass_event_lower_domination _ A (piMass_nonneg μ hμ) a ha hA) hcap

theorem rough_dominated_pi_mass_fiber_union_tendsto {ι α : Type*} [Fintype ι]
    (μ : ℕ → ι → Mass α) (ρ : ℕ → Mass (ι → α)) (E : ℕ → ι → (ι → α) → Prop)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hμ : ∀ᶠ w in atTop, ∀ i x, 0 ≤ μ w i x)
    (ht : ∀ᶠ w in atTop, ∀ i, total (μ w i)=1)
    (hρ : ∀ᶠ w in atTop, ∀ x, 0 ≤ ρ w x)
    (hdom : ∀ᶠ w in atTop, ∀ x, ρ w x ≤ C₀*piMass (μ w) x)
    (hcap : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ i,
      ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ w j.val)).support,
        event (μ w i) (fun value => E w i (insertPivotCoordinate i rest value)) ≤ ε) :
    Tendsto (fun w => event (ρ w) (fun x => ∃ i, E w i x)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [hρ] with w hw
    exact hb.trans_le (event_nonneg _ _ hw)
  · intro δ hδ
    let ε := δ/(C₀*(Fintype.card ι : ℝ)+1)
    have hden : 0 < C₀*(Fintype.card ι : ℝ)+1 := by positivity
    have hε : 0 < ε := div_pos hδ hden
    have heq : (C₀*(Fintype.card ι : ℝ)+1)*ε=δ := by dsimp only [ε]; field_simp
    filter_upwards [hμ,ht,hdom,hcap ε hε] with w hμw htw hdomw hcapw
    have hu := rough_dominated_pi_mass_coordinate_union_le (μ w) (ρ w) (E w)
      hμw htw C₀ ε hC₀ hdomw hcapw
    nlinarith

theorem rough_conditioned_pi_mass_fiber_union_tendsto {ι α : Type*} [Fintype ι]
    (μ : ℕ → ι → Mass α) (A : ℕ → (ι → α) → Prop) (E : ℕ → ι → (ι → α) → Prop)
    (a : ℝ) (ha : 0 < a)
    (hμ : ∀ᶠ w in atTop, ∀ i x, 0 ≤ μ w i x)
    (ht : ∀ᶠ w in atTop, ∀ i, total (μ w i)=1)
    (hA : ∀ᶠ w in atTop, a ≤ event (piMass (μ w)) (A w))
    (hcap : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ i,
      ∀ rest ∈ (piMass (fun j : {j : ι // j ≠ i} => μ w j.val)).support,
        event (μ w i) (fun value => E w i (insertPivotCoordinate i rest value)) ≤ ε) :
    Tendsto (fun w => event (conditionMass (piMass (μ w)) (A w))
      (fun x => ∃ i, E w i x)) atTop (𝓝 0) := by
  apply rough_dominated_pi_mass_fiber_union_tendsto μ _ E a⁻¹ (inv_nonneg.mpr ha.le) hμ ht _ _ hcap
  · filter_upwards [hμ] with w hw
    exact conditionMass_nonneg _ _ (piMass_nonneg _ hw)
  · filter_upwards [hμ,hA] with w hw haW
    exact rough_condition_mass_event_lower_domination _ _ (piMass_nonneg _ hw) a ha haW

end Hindman168
