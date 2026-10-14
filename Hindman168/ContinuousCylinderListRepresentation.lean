import Hindman168.CompactLipschitzAlgebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.Submonoid.Membership

/-! Every actual star-algebra cylinder test is a finite complex coefficient
combination of finite lists of ORIGINAL generators. Conjugate generators
are returned to their original family by PROVED star closure. -/
namespace Hindman168
open scoped Classical Pointwise
variable {Y : Type*} [TopologicalSpace Y]

noncomputable def continuousCylinderLinearCombination
    (terms : List (ℂ × List C(Y,ℂ))) : C(Y,ℂ) :=
  (terms.map (fun t => t.1 • t.2.prod)).sum

theorem continuous_cylinder_linear_combination_append (l m : List (ℂ × List C(Y,ℂ))) :
    continuousCylinderLinearCombination (l++m)=
      continuousCylinderLinearCombination l+continuousCylinderLinearCombination m := by
  simp only [continuousCylinderLinearCombination,List.map_append,List.sum_append]

theorem continuous_cylinder_linear_combination_smul (c : ℂ) (l : List (ℂ × List C(Y,ℂ))) :
    continuousCylinderLinearCombination (l.map (fun t => (c*t.1,t.2)))=
      c • continuousCylinderLinearCombination l := by
  simp only [continuousCylinderLinearCombination,List.map_map,List.smul_sum]
  congr 1
  congr 1
  funext t
  exact mul_smul c t.1 t.2.prod

theorem continuous_star_cylinder_list_representation (S : Set C(Y,ℂ))
    (hstar : ∀ f ∈ S, star f ∈ S) (F : C(Y,ℂ)) (hF : F ∈ StarAlgebra.adjoin ℂ S) :
    ∃ l : List (ℂ × List C(Y,ℂ)), (∀ t ∈ l, ∀ f ∈ t.2, f ∈ S) ∧
      F=continuousCylinderLinearCombination l := by
  have hstarS : star S ⊆ S := by
    intro f hf
    simpa only [star_star] using hstar (star f) (Set.mem_star.mp hf)
  change F ∈ (StarAlgebra.adjoin ℂ S).toSubalgebra.toSubmodule at hF
  rw [StarAlgebra.adjoin_eq_span] at hF
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨readings,hreadings,he⟩ := Submonoid.exists_list_of_mem_closure hf
    refine ⟨[(1,readings)],?_,?_⟩
    · intro t ht
      have ht' : t=(1,readings) := List.mem_singleton.mp ht
      subst t
      intro g hg
      exact (hreadings g hg).elim id (fun h => hstarS h)
    · rw [←he]
      simp only [continuousCylinderLinearCombination,List.map_singleton,List.sum_singleton,one_smul]
  | zero => exact ⟨[],by simp,by simp only [continuousCylinderLinearCombination,List.map_nil,List.sum_nil]⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨l,hl,hfl⟩ := ihf
    obtain ⟨m,hm,hgm⟩ := ihg
    refine ⟨l++m,?_,?_⟩
    · intro t ht
      exact (List.mem_append.mp ht).elim (hl t) (hm t)
    · rw [continuous_cylinder_linear_combination_append,hfl,hgm]
  | smul c f hf ih =>
    obtain ⟨l,hl,hfl⟩ := ih
    refine ⟨l.map (fun t => (c*t.1,t.2)),?_,?_⟩
    · intro t ht
      obtain ⟨oldTerm,hOld,hEq⟩ := List.mem_map.mp ht
      rw [←hEq]
      exact hl oldTerm hOld
    · rw [continuous_cylinder_linear_combination_smul,hfl]

end Hindman168
