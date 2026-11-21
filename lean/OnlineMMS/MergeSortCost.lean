import Mathlib.Data.Nat.Size
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace OnlineMMS

/-- Comparator calls in the specification of Lean's stable list merge. -/
def mergeComparisons (le : α → α → Bool) : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    1 + if le x y then mergeComparisons le xs (y :: ys)
      else mergeComparisons le (x :: xs) ys

theorem mergeComparisons_le (le : α → α → Bool) (xs ys : List α) :
    mergeComparisons le xs ys ≤ xs.length + ys.length := by
  cases xs with
  | nil => simp [mergeComparisons]
  | cons x xs =>
    cases ys with
    | nil => simp [mergeComparisons]
    | cons y ys =>
      unfold mergeComparisons
      by_cases h : le x y = true
      · rw [if_pos h]
        have hh := mergeComparisons_le le xs (y :: ys)
        simp only [List.length_cons] at hh ⊢
        omega
      · rw [if_neg h]
        have hh := mergeComparisons_le le (x :: xs) ys
        simp only [List.length_cons] at hh ⊢
        omega
termination_by xs.length + ys.length

/-- Comparator calls in merge sort. The recurrence uses the same split and
the same sorted sublists as `List.mergeSort`. -/
def mergeSortComparisons (le : α → α → Bool) : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: xs =>
    let lr := List.MergeSort.Internal.splitInTwo (n := (a :: b :: xs).length)
      ⟨a :: b :: xs, rfl⟩
    have := lr.1.2
    have := lr.2.2
    mergeSortComparisons le lr.1.1 + mergeSortComparisons le lr.2.1 +
      mergeComparisons le (lr.1.1.mergeSort le) (lr.2.1.mergeSort le)
termination_by xs => xs.length
decreasing_by
  all_goals simp only [List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.length_take,
    List.length_drop, List.length_cons] at *
  all_goals omega

private theorem mergeSortComparisons_pow (le : α → α → Bool) (e : ℕ)
    (xs : List α) (h : xs.length ≤ 2^e) :
    mergeSortComparisons le xs ≤ e * xs.length := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [mergeSortComparisons]
    | cons a xs =>
      cases xs with
      | nil => simp [mergeSortComparisons]
      | cons b ys => simp at h
  | succ e ih =>
    cases xs with
    | nil => simp [mergeSortComparisons]
    | cons a xs =>
      cases xs with
      | nil => simp [mergeSortComparisons]
      | cons b ys =>
        let all := a :: b :: ys
        let lr := List.MergeSort.Internal.splitInTwo (n := all.length) ⟨all, rfl⟩
        have hl := lr.1.2
        have hr := lr.2.2
        have htotal : lr.1.1.length + lr.2.1.length = all.length := by omega
        have hpow : all.length ≤ 2^e * 2 := by simpa only [pow_succ] using h
        have hL := ih lr.1.1 (by omega)
        have hR := ih lr.2.1 (by omega)
        have hc := mergeComparisons_le le (lr.1.1.mergeSort le) (lr.2.1.mergeSort le)
        rw [List.length_mergeSort, List.length_mergeSort, htotal] at hc
        unfold mergeSortComparisons
        change mergeSortComparisons le lr.1.1 + mergeSortComparisons le lr.2.1 +
          mergeComparisons le (lr.1.1.mergeSort le) (lr.2.1.mergeSort le) ≤
            (e + 1) * all.length
        calc
          _ ≤ e * lr.1.1.length + e * lr.2.1.length + all.length :=
            Nat.add_le_add (Nat.add_le_add hL hR) hc
          _ = _ := by rw [← Nat.mul_add, htotal, Nat.add_mul, one_mul]

/-- Merge sorting n items makes at most n times its binary digit count
comparisons, independent of the comparator or ties. -/
theorem mergeSortComparisons_le (le : α → α → Bool) (xs : List α) :
    mergeSortComparisons le xs ≤ xs.length.size * xs.length :=
  mergeSortComparisons_pow le _ xs (Nat.lt_size_self _).le

end OnlineMMS
