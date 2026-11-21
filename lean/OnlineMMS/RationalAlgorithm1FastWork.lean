import OnlineMMS.RationalAlgorithm1Fast
import OnlineMMS.BucketRunningCost

namespace OnlineMMS.RationalAlgorithm1

open BucketBitComplexity
open private widthQ qCoeff cCoeff eligible from OnlineMMS.RationalAlgorithm1
open private fastSmall fastBuckets fastBuckets_eq sampleFast from OnlineMMS.RationalAlgorithm1Fast

/-- Charge the length-carrying splitter for its test and for scanning the
full block twice, once for take and once for drop. -/
def blockScanWork (width : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, count =>
    if count < width then 1
    else 2 * width + 3 + blockScanWork width fuel (count - width)

theorem blockScanWork_le {width : ℕ} (hw : 0 < width) (fuel count : ℕ) :
    blockScanWork width fuel count ≤ 5 * count + 1 := by
  induction fuel generalizing count with
  | zero => simp [blockScanWork]
  | succ fuel ih =>
    unfold blockScanWork
    split
    · omega
    · have h := ih (count - width)
      omega

/-- The trim shares one index sort across all rows. Each row initializes a
vector, sums the retained weights, and scans the shared order once. -/
def fastTrimWork {m : ℕ} (k : ℕ) (R : Finset (Fin m)) : ℕ :=
  indexSortBudget R.card + k * (m + R.card + 4 * R.card + 3)

private theorem indexSortBudget_mono {a b : ℕ} (h : a ≤ b) :
    indexSortBudget a ≤ indexSortBudget b :=
  Nat.mul_le_mul (Nat.size_le_size h) h

theorem fastTrimWork_le {m : ℕ} (k : ℕ) (R : Finset (Fin m)) :
    fastTrimWork k R ≤ indexSortBudget m + 6 * k * (m + 1) := by
  have hc : R.card ≤ m := by simpa using R.card_le_univ
  unfold fastTrimWork
  apply Nat.add_le_add (indexSortBudget_mono hc)
  calc
    _ ≤ k * (6 * (m + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

/-- One call of the optimized transition, with charges for exact rational
arithmetic, comparisons and linear scans of goods. Array indexing/marking is
unit-cost in the scan budget. Preprocessing and instrumentation overhead
are outside the per-arrival count. -/
def advanceFastCounted {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ)
    (r : ℕ) (x : State m k) (t : Fin k) :
    (Finset (Fin m) × State m k) × ℕ :=
  if r = 0 then ((x.remaining, {x with remaining := ∅}), 1)
  else if 0 < d t then
    let goods := eligible h x t
    let base := 12 + 8 * x.remaining.card
    if hn : goods.Nonempty then
      let g := goods.min' hn
      let R := x.remaining.erase g
      (({g}, fastSmall r x R), base + x.remaining.card + fastTrimWork k R)
    else
      let H := widthQ h b r x
      let buckets := fastBuckets (x.weight t) H x.remaining
      let run := selectLinearCounted x.weight h (qCoeff x) (cCoeff h x) x.products buckets
      let n := x.remaining.card
      -- Two sorts (initial index order, then by value), block splitting,
      -- one mark vector, two filters, and the stored-product update.
      (sampleFast h x run.1,
       base + 2 * indexSortBudget n + blockScanWork H n n + run.2 +
         m + run.1.length + 2 * n + k * (4 * run.1.length + 2))
  else ((∅, fastSmall r x x.remaining), 2 + fastTrimWork k x.remaining)

theorem advanceFastCounted_result {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ)
    (r : ℕ) (x : State m k) (t : Fin k) :
    (advanceFastCounted h b d r x t).1 = advanceFast h b d r x t := by
  by_cases hr : r = 0
  · simp [advanceFastCounted, advanceFast, hr]
  by_cases ht : 0 < d t
  · by_cases he : (eligible h x t).Nonempty
    · simp [advanceFastCounted, advanceFast, hr, ht, he]
    · simp [advanceFastCounted, advanceFast, hr, ht, he, selectLinearCounted_result]
  · simp [advanceFastCounted, advanceFast, hr, ht]

/-- A pointwise bound for every legal optimized arrival, including the final,
zero-TPS, singleton, and sampling branches. -/
theorem advanceFastCounted_bound {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k)
    (hx : ∀ i g, 0 ≤ x.weight i g) :
    (advanceFastCounted h b d r x t).2 ≤
      64 * (k * (m + 1) + m * ((m + 2).log2 + 1)) := by
  let K := k * (m + 1)
  let S := indexSortBudget m
  have hk : 0 < k := by have := t.isLt; omega
  have hK : m + 1 ≤ K := Nat.le_mul_of_pos_left _ hk
  have hc : x.remaining.card ≤ m := by simpa using x.remaining.card_le_univ
  have hsort : indexSortBudget x.remaining.card ≤ S := indexSortBudget_mono hc
  have hl : m.size ≤ (m + 2).log2 + 1 := by
    apply Nat.size_le.mpr
    exact (show m < m + 2 by omega).trans_le
      ((Nat.log2_lt (show m + 2 ≠ 0 by omega)).mp (by omega)).le
  have hS : S ≤ m * ((m + 2).log2 + 1) := by
    unfold S indexSortBudget
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right m hl
  suffices h : (advanceFastCounted h b d r x t).2 ≤ 64 * (K + S) from
    h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hS _))
  by_cases hr : r = 0
  · simp only [advanceFastCounted, if_pos hr]
    omega
  by_cases ht : 0 < d t
  · let goods := eligible h x t
    by_cases he : (eligible h x t).Nonempty
    · have htrim := fastTrimWork_le k (x.remaining.erase (goods.min' he))
      change fastTrimWork k (x.remaining.erase (goods.min' he)) ≤ S + 6 * k * (m + 1) at htrim
      rw [Nat.mul_assoc] at htrim
      change fastTrimWork k (x.remaining.erase (goods.min' he)) ≤ S + 6 * K at htrim
      simp only [advanceFastCounted, if_neg hr, if_pos ht, dif_pos he]
      change 12 + 8 * x.remaining.card + x.remaining.card +
        fastTrimWork k (x.remaining.erase (goods.min' he)) ≤ 64 * (K + S)
      omega
    · let H := widthQ h b r x
      let buckets := fastBuckets (x.weight t) H x.remaining
      let run := selectLinearCounted x.weight h (qCoeff x) (cCoeff h x) x.products buckets
      have hp : 0 < H := by
        unfold H widthQ
        split <;> exact Nat.mul_pos (by assumption) (by omega)
      have hs : SortedBuckets (fun g => (x.weight t g : ℝ)) H x.remaining buckets := by
        rw [show buckets = rationalBuckets (x.weight t) H x.remaining from fastBuckets_eq ..]
        exact rationalBuckets_spec _ hp _
      have hne (B : Finset (Fin m)) (hB : B ∈ buckets) : B.Nonempty :=
        Finset.card_pos.mp (hs.bucket_size B hB ▸ hp)
      have hwork := selectLinearCounted_bound x.weight h (qCoeff x) (cCoeff h x)
        x.products buckets hne hs.pairwise_disjoint
      have hwork' : run.2 ≤ 36 * K + m + S := by
        simpa only [run, K, S, Nat.mul_assoc] using hwork
      have heq : run.1 = selectQ x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets :=
        (selectLinearCounted_result ..).trans
          (selectLinearQ_eq _ _ _ _ _ (by exact_mod_cast (show 1 ≤ h by omega)) hx _ _ hne)
      have hg := selectQ_greedy x.weight h (qCoeff x) (cCoeff h x) x.products buckets hne []
      have hchoose := (greedy_sample_le_mean _ _ _ _ _ _ _ hg).1
      rw [← heq] at hchoose
      have hselected := hs.selected_valid hchoose
      have hlen := List.toFinset_card_of_nodup hselected.2
      have hlen' : run.1.length ≤ m := by
        rw [← hlen]
        exact (Finset.card_le_card hselected.1).trans hc
      have hproduct : k * (4 * run.1.length + 2) ≤ 4 * K := by
        unfold K
        rw [Nat.mul_left_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      have hsplit := blockScanWork_le hp x.remaining.card x.remaining.card
      simp only [advanceFastCounted, if_neg hr, if_pos ht, dif_neg he]
      change 12 + 8 * x.remaining.card + 2 * indexSortBudget x.remaining.card +
        blockScanWork H x.remaining.card x.remaining.card + run.2 +
        m + run.1.length + 2 * x.remaining.card + k * (4 * run.1.length + 2) ≤ _
      omega
  · have htrim := fastTrimWork_le k x.remaining
    rw [Nat.mul_assoc] at htrim
    change fastTrimWork k x.remaining ≤ S + 6 * K at htrim
    simp only [advanceFastCounted, if_neg hr, if_neg ht]
    omega

/-- The same uniform estimate in the manuscript's real-log form. -/
theorem advanceFastCounted_log_bound {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k)
    (hx : ∀ i g, 0 ≤ x.weight i g) :
    ((advanceFastCounted h b d r x t).2 : ℝ) ≤
      (64 * max 1 (2 / Real.log 2)) *
        ((k : ℝ) * ((m : ℝ) + 1) + (m : ℝ) * Real.log ((m : ℝ) + 2)) := by
  let z := m + 2
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmin : Real.log (2 : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hpow : (2 : ℝ)^z.log2 ≤ (m : ℝ) + 2 := by
    have h : 2 ^ z.log2 ≤ z := (Nat.le_log2 (show z ≠ 0 by omega)).mp le_rfl
    exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hs : ((m + 2).log2 : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log ((m : ℝ) + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]
    change (z.log2 : ℝ) * Real.log 2 ≤ _ at hlog
    change ((z.log2 : ℝ) + 1) * Real.log 2 ≤ _
    nlinarith only [hlog, hmin]
  let C := max (1 : ℝ) (2 / Real.log 2)
  have hA : (k : ℝ) * ((m : ℝ) + 1) ≤ C * ((k : ℝ) * ((m : ℝ) + 1)) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 / Real.log 2)) (by positivity :
        0 ≤ (k : ℝ) * ((m : ℝ) + 1))
  have hB : (m : ℝ) * (((m + 2).log2 : ℝ) + 1) ≤ C * ((m : ℝ) * Real.log ((m : ℝ) + 2)) := by
    calc
      _ ≤ (m : ℝ) * ((2 / Real.log 2) * Real.log ((m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ = (2 / Real.log 2) * ((m : ℝ) * Real.log ((m : ℝ) + 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (Nat.cast_nonneg _) (h2.le.trans hmin))
  have hb := advanceFastCounted_bound hh hb d r x t hx
  calc
    _ ≤ (64 : ℝ) * ((k : ℝ) * ((m : ℝ) + 1) + (m : ℝ) * (((m + 2).log2 : ℝ) + 1)) := by
      exact_mod_cast hb
    _ ≤ _ := by
      change _ ≤ (64 * C) * _
      rw [mul_assoc, mul_add C]
      exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)

/-- The bound applies at every prefix of the rational policy's execution.
The two projections certify the result and the operation count of one call. -/
theorem fastPolicy_arrival_work {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g)
    (past : List (Fin k)) (t : Fin k) :
    let h := parameterQ k
    let d := materialize (fun t => rationalTPSFast (v t) n)
    let r := n - (past.length + 1)
    let x := policyState v n past
    let counted := advanceFastCounted h (h / 4) d r x t
    counted.1 = advanceFast h (h / 4) d r x t ∧
      counted.2 ≤ 64 * (k * (m + 1) + m * ((m + 2).log2 + 1)) := by
  obtain ⟨D, _, hState⟩ := policyState_gridHistory hn hk v hv
  have hh : 216 ≤ parameterQ k := by rw [parameterQ_eq]; exact (bucketMultiplier_bounds hk).1
  exact ⟨advanceFastCounted_result ..,
    advanceFastCounted_bound (by omega) (by omega) _ _ _ _
      (fun i g => ((hState past).weights i g).2.1)⟩

end OnlineMMS.RationalAlgorithm1
