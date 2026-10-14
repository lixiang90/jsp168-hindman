import Hindman168.FiniteComplexMassMean

/-! Actual retained finite coefficient sums control original product errors;
zero coefficients and empty lists are retained exactly. -/
namespace Hindman168
open scoped Classical

theorem finite_complex_list_coefficient_error {α : Type*} (l : List α)
    (coefficient error : α → ℂ) (ε : ℝ)
    (herror : ∀ t ∈ l, ‖error t‖ ≤ ε) :
    ‖(l.map (fun t => coefficient t*error t)).sum‖ ≤
      (l.map (fun t => ‖coefficient t‖)).sum*ε := by
  induction l with
  | nil => simp only [List.map_nil,List.sum_nil,norm_zero,zero_mul,le_refl]
  | cons t l ih =>
    have ht : ‖error t‖ ≤ ε := herror t (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, ‖error x‖ ≤ ε := fun x hx => herror x (List.mem_cons_of_mem t hx)
    rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons]
    calc
      _ ≤ ‖coefficient t*error t‖+‖(l.map (fun t => coefficient t*error t)).sum‖ := norm_add_le _ _
      _ ≤ ‖coefficient t‖*ε+(l.map (fun t => ‖coefficient t‖)).sum*ε :=
        add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)) (ih hl)
      _ = _ := by ring

theorem finite_complex_list_positive_budget {α : Type*} (l : List α)
    (coefficient error : α → ℂ) (ε R : ℝ) (hε : 0 < ε)
    (hsize : (l.map (fun t => ‖coefficient t‖)).sum < R)
    (herror : ∀ t ∈ l, ‖error t‖ ≤ ε) :
    ‖(l.map (fun t => coefficient t*error t)).sum‖ < R*ε :=
  (finite_complex_list_coefficient_error l coefficient error ε herror).trans_lt
    (mul_lt_mul_of_pos_right hsize hε)

theorem finite_complex_list_linear_difference {α : Type*} (l : List α)
    (coefficient a b : α → ℂ) :
    (l.map (fun t => coefficient t*a t)).sum-(l.map (fun t => coefficient t*b t)).sum=
      (l.map (fun t => coefficient t*(a t-b t))).sum := by
  induction l with
  | nil => simp only [List.map_nil,List.sum_nil,sub_self]
  | cons t l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [←ih]
    ring

end Hindman168
