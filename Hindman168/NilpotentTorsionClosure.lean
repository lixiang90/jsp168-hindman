import Hindman168.FiniteTorsionGenerators
import Mathlib.GroupTheory.Nilpotent

/-! In an arbitrary actual nilpotent group, a finite set of finite-order
elements generates a finite subgroup. Induction uses the actual center
quotient, its finite generated image, a genuine central kernel,
Schur's theorem and the finite abelianization of torsion generators.
Consequently finite-order elements are closed under multiplication. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

theorem nilpotent_finite_closure_of_torsion (s : Set G)
    (hsf : s.Finite) (ht : ∀ g ∈ s, IsOfFinOrder g) :
    Finite (Subgroup.closure s) := by
  apply @Group.nilpotent_center_quotient_ind
    (fun G _ _ => ∀ s : Set G, s.Finite →
      (∀ g ∈ s, IsOfFinOrder g) → Finite (Subgroup.closure s))
    G _ _ ?_ ?_ s hsf ht
  · intro G _ _ s _ _
    infer_instance
  · intro G _ _ ih s hsf ht
    let q := QuotientGroup.mk' (Subgroup.center G)
    let K := Subgroup.closure s
    let f := q.comp K.subtype
    have himage : Finite (Subgroup.closure (q '' s)) := by
      apply ih _ (hsf.image q)
      rintro x ⟨g, hg, rfl⟩
      exact q.isOfFinOrder (ht g hg)
    have hr : f.range = Subgroup.closure (q '' s) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure]
    letI : Finite f.range := hr.symm ▸ himage
    have hker : f.ker ≤ Subgroup.center K := by
      intro z hz
      have hzq : q z.val = 1 := hz
      have hzc : z.val ∈ Subgroup.center G := (QuotientGroup.eq_one_iff z.val).mp hzq
      apply Subgroup.mem_center_iff.mpr
      intro k
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzc k.val
    letI : f.ker.FiniteIndex := inferInstance
    letI : (Subgroup.center K).FiniteIndex := Subgroup.finiteIndex_of_le hker
    letI : Finite (K ⧸ Subgroup.center K) := inferInstance
    letI : Finite (_root_.commutator K) :=
      finite_commutator_of_finite_center_quotient
    let t : Set K := K.subtype ⁻¹' s
    have htf : t.Finite := Set.Finite.preimage Subtype.val_injective.injOn hsf
    have htc : Subgroup.closure t = ⊤ := Subgroup.closure_preimage_eq_top s
    have htt : ∀ k ∈ t, IsOfFinOrder k := by
      intro k hk
      exact (show Function.Injective K.subtype from Subtype.val_injective).isOfFinOrder_iff.mp
        (ht k.val hk)
    exact finite_of_finite_commutator_torsion_generators t htf htc htt

theorem nilpotent_finite_of_fg_torsion (G : Type*) [Group G]
    [Group.IsNilpotent G] [Group.FG G] (ht : Monoid.IsTorsion G) : Finite G := by
  obtain ⟨s, hs, hsf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  have hf := nilpotent_finite_closure_of_torsion s hsf (fun g _ => ht g)
  rw [hs] at hf
  letI : Finite (⊤ : Subgroup G) := hf
  exact Finite.of_surjective (⊤ : Subgroup G).subtype
    (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)

theorem nilpotent_finiteOrder_mul {a b : G}
    (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) : IsOfFinOrder (a * b) := by
  let s : Set G := {a, b}
  have hs : s.Finite := by simp [s]
  have ht : ∀ g ∈ s, IsOfFinOrder g := by
    intro g hg
    rcases hg with rfl | hg
    · exact ha
    · exact (Set.mem_singleton_iff.mp hg) ▸ hb
  let K := Subgroup.closure s
  letI : Finite K := nilpotent_finite_closure_of_torsion s hs ht
  have ham : a ∈ K := Subgroup.subset_closure (by simp [s])
  have hbm : b ∈ K := Subgroup.subset_closure (by simp [s])
  let x : K := ⟨a * b, K.mul_mem ham hbm⟩
  exact K.subtype.isOfFinOrder (isTorsion_of_finite x)

end Hindman168
