import Hindman168.RoughIntervalPartition

namespace Hindman168
open scoped Classical

def roughResidueLabel (K : ℕ) (hK : 0 < K) (x : ℤ) : Fin K :=
  ⟨(x % (K : ℤ)).toNat, by
    have hp : (0 : ℤ) < K := by exact_mod_cast hK
    have h0 := Int.emod_nonneg x hp.ne'
    have hh : ((x % (K : ℤ)).toNat : ℤ) < K := by
      rw [Int.toNat_of_nonneg h0]
      exact Int.emod_lt_of_pos x hp
    exact_mod_cast hh⟩

theorem rough_residue_label_iff (K : ℕ) (hK : 0 < K) (x : ℤ) (u : Fin K) :
    roughResidueLabel K hK x = u ↔ Int.ModEq (K : ℤ) x (u.val : ℤ) := by
  have hp : (0 : ℤ) < K := by exact_mod_cast hK
  have h0 := Int.emod_nonneg x hp.ne'
  have hu : (0 : ℤ) ≤ u.val := by positivity
  have hult : (u.val : ℤ) < K := by exact_mod_cast u.isLt
  rw [Fin.ext_iff]
  change (x % (K : ℤ)).toNat = u.val ↔ x % (K : ℤ) = (u.val : ℤ) % K
  rw [Int.emod_eq_of_lt hu hult]
  constructor
  · intro h
    have hh : ((x % (K : ℤ)).toNat : ℤ) = u.val := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg h0] using hh
  · intro h
    have hh : ((x % (K : ℤ)).toNat : ℤ) = u.val := by
      simpa only [Int.toNat_of_nonneg h0] using h
    exact_mod_cast hh

noncomputable def roughBoxLabel {ι : Type*} (A B : ι → ℤ) (N K : ℕ)
    (hN : 0 < N) (hK : 0 < K) (x : ι → ℤ) : (ι → Fin N) × (ι → Fin K) :=
  ⟨fun j => roughIntervalLabel (A j) (B j) N hN (x j),
    fun j => roughResidueLabel K hK (x j)⟩

def roughBoxLower {ι : Type*} (A B : ι → ℤ) (N : ℕ) (i : ι → Fin N) : ι → ℤ :=
  fun j => roughBalancedCut (A j) (B j) N (i j).val

def roughBoxUpper {ι : Type*} (A B : ι → ℤ) (N : ℕ) (i : ι → Fin N) : ι → ℤ :=
  fun j => roughBalancedCut (A j) (B j) N ((i j).val+1)

theorem rough_box_label_fiber {ι : Type*} [Fintype ι] (A B a : ι → ℤ)
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (hAB : ∀ j, A j ≤ B j)
    (t : ℤ) (p : (ι → Fin N) × (ι → Fin K)) :
    (alignmentBoxClass A B a t).filter (fun x => roughBoxLabel A B N K hN hK x = p) =
      alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
      alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
        (fun j => ((p.2 j).val : ℤ)) K := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, alignmentBoxClass, Fintype.mem_piFinset]
  constructor
  · intro hx
    have he := Prod.mk.inj hx.2
    have hlabel : ∀ j, roughIntervalLabel (A j) (B j) N hN (x j) = p.1 j :=
      fun j => congrFun he.1 j
    have hres : ∀ j, roughResidueLabel K hK (x j) = p.2 j := fun j => congrFun he.2 j
    have hi : ∀ j, roughBalancedCut (A j) (B j) N (p.1 j).val ≤ x j ∧
        x j < roughBalancedCut (A j) (B j) N ((p.1 j).val+1) := by
      intro j
      have hj := (Finset.mem_filter.mp (hx.1 j)).1
      exact (rough_interval_label_iff _ _ N hN (hAB j) (x j) (Finset.mem_Ico.mp hj) _).mp (hlabel j)
    constructor
    · intro j
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hi j), (Finset.mem_filter.mp (hx.1 j)).2⟩
    · intro j
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hi j),
        ((rough_residue_label_iff K hK (x j) (p.2 j)).mp (hres j)).symm⟩
  · intro hx
    have hm : ∀ j, x j ∈ alignmentIntervalClass (A j) (B j) t (a j) := by
      intro j
      exact rough_interval_class_subwindow _ _ _ _ _ _
        (rough_balanced_cut_contained _ _ N _ (hAB j) hN (p.1 j).isLt.le).1
        (rough_balanced_cut_contained _ _ N _ (hAB j) hN (by omega)).2 (hx.1 j)
    refine ⟨hm, ?_⟩
    apply Prod.ext
    · funext j
      have hp := Finset.mem_Ico.mp (Finset.mem_filter.mp (hm j)).1
      exact (rough_interval_label_iff _ _ N hN (hAB j) (x j) hp _).mpr
        (Finset.mem_Ico.mp (Finset.mem_filter.mp (hx.1 j)).1)
    · funext j
      exact (rough_residue_label_iff K hK (x j) (p.2 j)).mpr
        (Finset.mem_filter.mp (hx.2 j)).2.symm

theorem rough_box_unrestricted_label_fiber {ι : Type*} [Fintype ι] (A B : ι → ℤ)
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (hAB : ∀ j, A j ≤ B j)
    (p : (ι → Fin N) × (ι → Fin K)) :
    (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).filter
      (fun x => roughBoxLabel A B N K hN hK x = p) =
      alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
        (fun j => ((p.2 j).val : ℤ)) K := by
  have hh := rough_box_label_fiber A B (fun _ => 0) N K hN hK hAB 1 p
  have hfull : ∀ l r : ι → ℤ, alignmentBoxClass l r (fun _ => 0) 1 =
      Fintype.piFinset (fun j => Finset.Ico (l j) (r j)) := by
    intro l r
    simp [alignmentBoxClass, alignmentIntervalClass, Int.ModEq]
  simp only [hfull] at hh
  rw [hh]
  apply Finset.inter_eq_right.mpr
  intro x hx
  exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx j)).1)

end Hindman168
