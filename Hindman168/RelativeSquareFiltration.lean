import Hindman168.RelativeSquareSubgroup

/-! Actual relative-square filtration. Its next-layer comparison condition
is essential: the full product filtration does not have this degree drop. -/

namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

def relativeSquareFiltration (F : ℕ → Subgroup G) (hN : ∀ i, (F i).Normal)
    (i : ℕ) : Subgroup (G × G) :=
  letI := hN (i+1)
  relativeSquareSubgroup (F i) (F (i+1))

theorem relative_square_filtration_mem_iff (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (i : ℕ) (p : G × G) :
    p ∈ relativeSquareFiltration F hN i ↔
      p.1 ∈ F i ∧ p.2 ∈ F i ∧ p.2⁻¹ * p.1 ∈ F (i+1) := by
  letI := hN (i+1)
  exact relative_square_mem_iff (F i) (F (i+1)) p

theorem relative_square_filtration_antitone (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) :
    Antitone (relativeSquareFiltration F hN) := by
  intro i j hij p hp
  obtain ⟨h1,h2,h3⟩ := (relative_square_filtration_mem_iff F hN j p).mp hp
  exact (relative_square_filtration_mem_iff F hN i p).mpr
    ⟨hF.antitone hij h1,hF.antitone hij h2,hF.antitone (Nat.add_le_add_right hij 1) h3⟩

theorem relative_square_filtration_commutator (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F)
    (i j : ℕ) (p : G × G) (hp : p ∈ relativeSquareFiltration F hN i)
    (q : G × G) (hq : q ∈ relativeSquareFiltration F hN j) :
    ⁅p,q⁆ ∈ relativeSquareFiltration F hN (i+j) := by
  obtain ⟨hp1,hp2,hpe⟩ := (relative_square_filtration_mem_iff F hN i p).mp hp
  obtain ⟨hq1,hq2,hqf⟩ := (relative_square_filtration_mem_iff F hN j q).mp hq
  letI := hN (i+j+1)
  let π := QuotientGroup.mk' (F (i+j+1))
  have hec : ⁅π (p.2⁻¹*p.1),π q.1⁆ = 1 := by
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc := hF.commutator_mem (i+1) j _ hpe _ hq1
    simpa only [Nat.add_right_comm] using hc
  have hbf : ⁅π p.2,π (q.2⁻¹*q.1)⁆ = 1 := by
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc := hF.commutator_mem i (j+1) _ hp2 _ hqf
    simpa only [Nat.add_assoc] using hc
  have hep : π p.1 = π p.2 * π (p.2⁻¹*p.1) := by
    rw [← map_mul,mul_inv_cancel_left]
  have heq : π q.1 = π q.2 * π (q.2⁻¹*q.1) := by
    rw [← map_mul,mul_inv_cancel_left]
  have hc : π ⁅p.1,q.1⁆ = π ⁅p.2,q.2⁆ := by
    rw [map_commutatorElement,map_commutatorElement]
    calc
      ⁅π p.1,π q.1⁆ = ⁅π p.2 * π (p.2⁻¹*p.1),π q.1⁆ := by rw [hep]
      _ = ⁅π p.2,π q.1⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul,hec,mul_one,mul_inv_cancel,one_mul]
      _ = ⁅π p.2,π q.2 * π (q.2⁻¹*q.1)⁆ := by rw [heq]
      _ = ⁅π p.2,π q.2⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj,hbf,mul_one,mul_inv_cancel_right]
  apply (relative_square_filtration_mem_iff F hN (i+j) ⁅p,q⁆).mpr
  refine ⟨hF.commutator_mem i j _ hp1 _ hq1,hF.commutator_mem i j _ hp2 _ hq2,?_⟩
  have h := π.eq_iff.mp hc
  rwa [QuotientGroup.ker_mk'] at h

theorem relative_square_filtration_conditions (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) :
    CubeGroupFiltration (relativeSquareFiltration F hN) :=
  ⟨relative_square_filtration_antitone F hN hF,
    relative_square_filtration_commutator F hN hF⟩

theorem relative_square_filtration_terminal_diagonal (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (d : ℕ) (hd : F (d+1) = ⊥) :
    relativeSquareFiltration F hN d = relativeDiagonalSubgroup (F d) := by
  ext p
  rw [relative_square_filtration_mem_iff,relative_diagonal_mem_iff,hd,Subgroup.mem_bot,inv_mul_eq_one]
  constructor
  · rintro ⟨h1,_,he⟩
    exact ⟨h1,he.symm⟩
  · rintro ⟨h1,he⟩
    exact ⟨h1,he ▸ h1,he.symm⟩

end Hindman168
