import OnlineMMS.RationalAlgorithm1Cost
import OnlineMMS.MergeSortCost

namespace OnlineMMS.RationalAlgorithm1

open BucketBitComplexity
open private smallQ sampleQ widthQ qCoeff cCoeff eligible from OnlineMMS.RationalAlgorithm1

/-- Count one signed-rational trim query in the fixed index order. The
counter charges a comparison, a subtraction, and a maximum per visited
position; the scan stops at the queried good if it occurs. -/
def trimQueryWork (g : Fin m) : List (Fin m) → ℕ
  | [] => 0
  | a :: as => 3 + if g = a then 0 else trimQueryWork g as

theorem trimQueryWork_le (g : Fin m) (as : List (Fin m)) :
    trimQueryWork g as ≤ 3 * as.length := by
  induction as with
  | nil => simp [trimQueryWork]
  | cons a as ih =>
    unfold trimQueryWork
    by_cases h : g = a <;> simp only [h, if_true, if_false, List.length_cons] <;> omega

/-- One eager update of all k by m entries. The extra terms charge the
initial remaining-value sum and the fixed cap/removal arithmetic. -/
def trimTableWork {m : ℕ} (k : ℕ) (R : Finset (Fin m)) : ℕ :=
  k * ∑ g : Fin m, (R.card + 3 + trimQueryWork g (R.sort (· ≤ ·)))

theorem trimTableWork_le {m : ℕ} (k : ℕ) (R : Finset (Fin m)) :
    trimTableWork k R ≤ k * m * (4 * m + 3) := by
  unfold trimTableWork
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∑ _g : Fin m, (4 * m + 3) := by
      apply Finset.sum_le_sum
      intro g _
      have hc : R.card ≤ m := by simpa using R.card_le_univ
      have h := trimQueryWork_le g (R.sort (· ≤ ·))
      rw [Finset.length_sort] at h
      omega
    _ = _ := by simp

/-- A per-arrival counter for comparisons and rational operations, following
the branches of `advance`. Sorting comparisons are counted by the actual
merge recurrence. List and finite-set bookkeeping can use linear scans. -/
def arrivalWork {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ)
    (r : ℕ) (x : State m k) (t : Fin k) : ℕ :=
  if r = 0 then 1
  else if 0 < d t then
    let base := 10 + 3 * x.remaining.card
    let goods := eligible h x t
    if hn : goods.Nonempty then
      base + trimTableWork k (x.remaining.erase (goods.min' hn))
    else
      let sorted := x.remaining.sort (· ≤ ·)
      let buckets := rationalBuckets (x.weight t) (widthQ h b r x) x.remaining
      let run := selectCosted x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets
      base + mergeSortComparisons (fun g i => decide (x.weight t i ≤ x.weight t g)) sorted +
        (x.remaining.card + 1)^2 + run.2 + k * (4 * run.1.length + 2)
  else 2 + trimTableWork k x.remaining

theorem arrivalWork_polynomial {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k) :
    arrivalWork h b d r x t ≤ 60 * (k + 1) * (m + 1)^3 := by
  have hm (R : Finset (Fin m)) : R.card ≤ m := by simpa using R.card_le_univ
  have htrim (R : Finset (Fin m)) :
      trimTableWork k R ≤ 5 * (k + 1) * (m + 1)^2 := by
    refine (trimTableWork_le k R).trans ?_
    calc
      k * m * (4 * m + 3) ≤ (k + 1) * (m + 1) * (5 * (m + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = _ := by ring
  have hc := hm x.remaining
  have hfactor : (m + 1)^2 ≤ (m + 1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hbound : 5 * (k + 1) * (m + 1)^2 ≤ 5 * (k + 1) * (m + 1)^3 :=
    Nat.mul_le_mul_left _ hfactor
  let U := (k + 1) * (m + 1)^3
  have hU : 0 < U := by unfold U; positivity
  have hmu : m + 1 ≤ U := by
    have h₁ : m + 1 ≤ (m + 1)^3 := by
      simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0 < m + 1)
        (show 1 ≤ 3 by decide))
    exact h₁.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hsq : (m + 1)^2 ≤ U := hfactor.trans (Nat.le_mul_of_pos_left _ (by omega))
  unfold arrivalWork
  by_cases hr : r = 0
  · rw [if_pos hr]
    rw [Nat.mul_assoc]
    change 1 ≤ 60 * U
    omega
  rw [if_neg hr]
  by_cases ht : 0 < d t
  · rw [if_pos ht]
    let goods := eligible h x t
    change (if hn : goods.Nonempty then _ else _) ≤ _
    by_cases hne : goods.Nonempty
    · rw [dif_pos hne]
      have hcost := (htrim (x.remaining.erase (goods.min' hne))).trans hbound
      change 10 + 3 * x.remaining.card + trimTableWork k (x.remaining.erase (goods.min' hne))
        ≤ 60 * (k + 1) * (m + 1)^3
      have hw : trimTableWork k (x.remaining.erase (goods.min' hne)) ≤ 5 * U := by
        simpa only [U, ← Nat.mul_assoc] using hcost
      rw [Nat.mul_assoc]
      change 10 + 3 * x.remaining.card + _ ≤ 60 * U
      omega
    · rw [dif_neg hne]
      let H := widthQ h b r x
      let bs := rationalBuckets (x.weight t) H x.remaining
      have hH : 0 < H := by unfold H widthQ; split <;> exact Nat.mul_pos (by assumption) (by omega)
      have hs := rationalBuckets_spec (x.weight t) hH x.remaining
      have hneB (B : Finset (Fin m)) (hB : B ∈ bs) : B.Nonempty :=
        Finset.card_pos.mp (hs.bucket_size B hB ▸ hH)
      have hC := candidateCount_le_goods bs hs.pairwise_disjoint
      have hloc : ([] : List (Fin k → ℚ)).length + bs.length ≤ m := by
        simpa only [List.length_nil, zero_add] using (length_le_candidateCount hneB).trans hC
      let run := selectCosted x.weight h (qCoeff x) (cCoeff h x) x.products [] bs
      obtain ⟨hg, hwork⟩ := selectCosted_certified x.weight h (qCoeff x) (cCoeff h x)
        x.products bs [] hneB hloc hC
      have hLength : run.1.length ≤ m := by
        have hf := (greedy_sample_le_mean _ _ _ _ _ _ _
          (show IsGreedySample _ _ _ _ _ [] bs run.1 from hg)).1
        rw [← hf.length_eq]
        simpa using hloc
      have hsort : mergeSortComparisons (fun g i => decide (x.weight t i ≤ x.weight t g))
            (x.remaining.sort (· ≤ ·)) ≤ (m + 1)^2 := by
        refine (mergeSortComparisons_le _ _).trans ?_
        rw [Finset.length_sort]
        have hm' : x.remaining.card.size ≤ m + 1 := by
          apply Nat.size_le.mpr
          exact hc.trans_lt ((Nat.lt_two_pow_self (n := m)).trans_le
            (Nat.pow_le_pow_right (by decide) (by omega)))
        exact (Nat.mul_le_mul hm' (show x.remaining.card ≤ m + 1 by omega)).trans_eq (by ring)
      have hblocks : (x.remaining.card + 1)^2 ≤ (m + 1)^2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hup : k * (4 * run.1.length + 2) ≤ 6 * U := by
        calc
          _ ≤ (k + 1) * (6 * (m + 1)) := Nat.mul_le_mul (by omega) (by omega)
          _ = 6 * ((k + 1) * (m + 1)) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (by simpa only [pow_one] using
              (Nat.pow_le_pow_right (by omega : 0 < m + 1) (show 1 ≤ 3 by decide))))
      have h1 := hsort.trans hsq
      have h2 := hblocks.trans hsq
      have h3 : run.2 ≤ 30 * U := by simpa only [U, ← Nat.mul_assoc] using hwork
      rw [Nat.mul_assoc]
      change 10 + 3 * x.remaining.card + _ + (x.remaining.card + 1)^2 + run.2 +
        k * (4 * run.1.length + 2) ≤ 60 * U
      omega
  · rw [if_neg ht]
    have hcost := (htrim x.remaining).trans hbound
    have hw : trimTableWork k x.remaining ≤ 5 * U := by
      simpa only [U, ← Nat.mul_assoc] using hcost
    rw [Nat.mul_assoc]
    change 2 + _ ≤ 60 * U
    omega

end OnlineMMS.RationalAlgorithm1
