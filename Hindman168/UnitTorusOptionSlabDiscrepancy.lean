import Hindman168.UnitTorusOptionSlabNeighborhood
import Hindman168.UnitTorusSetDistanceDiscrepancy

/-! Correct ACTUAL torus slab signal yields a TRUE unit-observable
discrepancy with fixed positive threshold before all raw slab/orbit inputs. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators Classical

theorem unit_torus_option_slab_discrepancy (ι : Type*) [Fintype ι]
    (Z δ : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ (β : ℝ) (ζ : Option ι → ℝ) (ε : ℝ),
      (∀ i, |ζ i| ≤ Z) → (∀ i, |ζ i| ≤ |ζ none|) → ζ none ≠ 0 → ε ≤ c*|ζ none| →
        ∀ {α : Type*} (s : Finset α), s.Nonempty → ∀ f : α → UnitAddTorus (Option ι),
          δ*(s.card : ℝ) ≤ (s.filter (fun a => f a ∈ unitTorusFractionalSlab β ζ ε)).card →
            ∃ F ∈ unitLipschitzObservables (UnitAddTorus (Option ι)), η ≤ ‖unitTorusFiniteDiscrepancy s f F‖ := by
  obtain ⟨r,c,hr,hr1,hc,hmeasure⟩ := unit_torus_option_slab_neighborhood ι Z δ hZ hδ hδ1
  refine ⟨c,δ*r/2,hc,by positivity,?_⟩
  intro β ζ ε hζ hmax hne hε α s hs f hdense
  have hS : (unitTorusFractionalSlab β ζ ε).Nonempty := by
    have hp : (0 : ℝ) < (s.filter (fun a => f a ∈ unitTorusFractionalSlab β ζ ε)).card :=
      lt_of_lt_of_le (mul_pos hδ (by exact_mod_cast hs.card_pos)) hdense
    have hne' : (s.filter (fun a => f a ∈ unitTorusFractionalSlab β ζ ε)).Nonempty :=
      Finset.card_pos.mp (by exact_mod_cast hp)
    obtain ⟨a,ha⟩ := hne'
    exact ⟨f a,(Finset.mem_filter.mp ha).2⟩
  exact ⟨unitTorusSetDistanceObservable r (unitTorusFractionalSlab β ζ ε),
    unit_torus_set_distance_observable_unit r hr.le hr1 _,
    unit_torus_set_distance_discrepancy s hs f _ hS r δ hr.le hδ.le hdense (hmeasure β ζ ε hζ hmax hne hε)⟩

end Hindman168
