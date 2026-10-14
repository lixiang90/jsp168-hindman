from pathlib import Path

source=Path('Hindman168/DenseCompleteIntervalBlock.lean').read_text(encoding='utf-8')
start=source.index('theorem dense_complete_interval_block')
body=source.index(' := by',start)
head='''theorem dense_fixed_length_interval_block (N K : ℕ) (hK : 0 < K) (hq : 0 < N/K)
    (δ : ℝ) (hδ : 0 < δ) (htail : 2*(K : ℝ) ≤ δ*(N : ℝ))
    (U : Finset ℕ) (hU : U ⊆ Finset.range N) (hdense : δ*(N : ℝ) ≤ U.card) :
    ∃ j : ℕ, j < N/K ∧ (j+1)*K ≤ N ∧
      (δ/2)*(K : ℝ) ≤ ((Finset.range K).filter (fun n => j*K+n ∈ U)).card'''
text=source[body:]
text=text.replace('  let L := N/J', '''  let J := N/K
  let L := K
  have hJ : 0 < J := hq
  have hL : 0 < L := hK''')
text=text.replace('by dsimp only [L]; simpa only [mul_comm] using Nat.div_mul_le_self N J',
                  'by dsimp only [J,L]; exact Nat.div_mul_le_self N K')
text=text.replace('have hRcard : R.card ≤ J', 'have hRcard : R.card ≤ K')
text=text.replace('(Finset.Ico (J*L) N).card ≤ J', '(Finset.Ico (J*L) N).card ≤ K')
text=text.replace('have he := Nat.mod_add_div N J','have he := Nat.mod_add_div N K')
text=text.replace('have hm := Nat.mod_lt N hJ','have hm := Nat.mod_lt N hK')
text=text.replace('dsimp only [L]\n      omega','dsimp only [J,L]\n      omega')
text=text.replace('''      have he := Nat.mod_add_div N K
      have hm := Nat.mod_lt N hK
      dsimp only [J,L]
      omega''','''      dsimp only [J,L]
      rw [← Nat.mod_eq_sub_div_mul]
      exact (Nat.mod_lt N hK).le''')
text=text.replace('have hr : (R.card : ℝ) ≤ J','have hr : (R.card : ℝ) ≤ K')
text=text.replace('simp only [hz,Nat.zero_div,lt_self_iff_false] at hL','simp only [hz,Nat.zero_div,lt_self_iff_false] at hq')
prefix=source[:start].replace('Actual complete short-block selection from dense original range hits.',
 'Actual FIXED-LENGTH complete block selection from dense original range hits.')
Path('Hindman168/DenseFixedLengthIntervalBlock.lean').write_text(prefix+head+text,encoding='utf-8')
