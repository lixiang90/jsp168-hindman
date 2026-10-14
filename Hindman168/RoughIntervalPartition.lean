import Hindman168.RoughBalancedCuts

namespace Hindman168
open scoped Classical

theorem rough_interval_cuts_cover (c : ℕ → ℤ) (N : ℕ) (x : ℤ)
    (hx : c 0 ≤ x ∧ x < c N) :
    ∃ i : Fin N, c i.val ≤ x ∧ x < c (i.val + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : x < c N
    · obtain ⟨i, hi⟩ := ih ⟨hx.1, h⟩
      exact ⟨⟨i.val, by omega⟩, hi⟩
    · exact ⟨⟨N, by omega⟩, by simpa using And.intro (le_of_not_gt h) hx.2⟩

theorem rough_interval_cuts_unique (c : ℕ → ℤ) (hc : Monotone c) (N : ℕ)
    (x : ℤ) (i j : Fin N)
    (hi : c i.val ≤ x ∧ x < c (i.val+1))
    (hj : c j.val ≤ x ∧ x < c (j.val+1)) : i = j := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hh := hc (show i.val+1 ≤ j.val by omega)
    omega
  · have hh := hc (show j.val+1 ≤ i.val by omega)
    omega

noncomputable def roughIntervalLabel (A B : ℤ) (N : ℕ) (hN : 0 < N) (x : ℤ) : Fin N :=
  if h : ∃ i : Fin N, roughBalancedCut A B N i.val ≤ x ∧
      x < roughBalancedCut A B N (i.val+1)
  then Classical.choose h else ⟨0, hN⟩

theorem rough_interval_label_spec (A B : ℤ) (N : ℕ) (hN : 0 < N)
    (hAB : A ≤ B) (x : ℤ) (hx : A ≤ x ∧ x < B) :
    roughBalancedCut A B N (roughIntervalLabel A B N hN x).val ≤ x ∧
      x < roughBalancedCut A B N ((roughIntervalLabel A B N hN x).val+1) := by
  have he := rough_balanced_cut_endpoints A B N hAB hN
  have hh := rough_interval_cuts_cover (roughBalancedCut A B N) N x
    (by simpa only [he.1, he.2] using hx)
  simp only [roughIntervalLabel, dif_pos hh]
  exact Classical.choose_spec hh

theorem rough_interval_label_iff (A B : ℤ) (N : ℕ) (hN : 0 < N)
    (hAB : A ≤ B) (x : ℤ) (hx : A ≤ x ∧ x < B) (i : Fin N) :
    roughIntervalLabel A B N hN x = i ↔
      roughBalancedCut A B N i.val ≤ x ∧ x < roughBalancedCut A B N (i.val+1) := by
  constructor
  · intro hi
    simpa only [hi] using rough_interval_label_spec A B N hN hAB x hx
  · intro hi
    exact rough_interval_cuts_unique _ (rough_balanced_cut_mono A B N) N x _ i
      (rough_interval_label_spec A B N hN hAB x hx) hi

theorem rough_interval_label_fiber (A B a d : ℤ) (N : ℕ) (hN : 0 < N)
    (hAB : A ≤ B) (i : Fin N) :
    (alignmentIntervalClass A B d a).filter (fun x => roughIntervalLabel A B N hN x = i) =
      alignmentIntervalClass (roughBalancedCut A B N i.val)
        (roughBalancedCut A B N (i.val+1)) d a := by
  ext x
  have hl := rough_balanced_cut_contained A B N i.val hAB hN i.isLt.le
  have hr := rough_balanced_cut_contained A B N (i.val+1) hAB hN (by omega)
  simp only [alignmentIntervalClass, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · intro hx
    exact ⟨(rough_interval_label_iff A B N hN hAB x hx.1.1 i).mp hx.2, hx.1.2⟩
  · intro hx
    have hp : A ≤ x ∧ x < B := ⟨hl.1.trans hx.1.1, hx.1.2.trans_le hr.2⟩
    exact ⟨⟨hp, hx.2⟩, (rough_interval_label_iff A B N hN hAB x hp i).mpr hx.1⟩

end Hindman168
