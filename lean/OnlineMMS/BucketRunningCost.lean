import OnlineMMS.BucketRunningScores
import OnlineMMS.MergeSortCost
import OnlineMMS.RationalAlgorithm1Cost

namespace OnlineMMS.BucketBitComplexity

open RationalAlgorithm1 (materialize)
open private summarizeQ replaceStats runningChoice selectRunningQ
  from OnlineMMS.BucketRunningScores

/-- Every list representative uses at most this many merge comparisons. -/
def indexSortBudget (size : ℕ) : ℕ := size.size * size

theorem indexSortBudget_rep {m : ℕ} (R : Finset (Fin m)) (l : List (Fin m))
    (hl : (l : Multiset (Fin m)) = R.val) :
    mergeSortComparisons (fun a b => decide (a ≤ b)) l ≤ indexSortBudget R.card := by
  have he : l.length = R.card := congrArg Multiset.card hl
  simpa only [indexSortBudget, he] using
    (mergeSortComparisons_le (fun a b => decide (a ≤ b)) l)

/-- Twelve operations per cached coefficient, two dot products and one
comparison per argmin step, and the index sort. -/
def runningTrialBudget (k goods : ℕ) : ℕ :=
  12 * k + (4 * k + 1) * goods + indexSortBudget goods

/-- A successful branch updates the stored sums and products once. -/
private def countRunningQ {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) :
    ConditionalStats k → List (Finset (Fin m) × (Fin k → ℚ)) → List (Fin m) × ℕ
  | _, [] => ([], 0)
  | S, (B, u) :: bs =>
    let cost := runningTrialBudget k B.card
    match runningChoice w h q c P S B u with
    | none =>
      let result := countRunningQ w h q c P S bs
      (result.1, cost + result.2)
    | some g =>
      let result := countRunningQ w h q c P (replaceStats h u (fun t => w t g) S) bs
      (g :: result.1, cost + 10 * k + result.2)

private theorem countRunningQ_result {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (S : ConditionalStats k) (bs : List (Finset (Fin m) × (Fin k → ℚ))) :
    (countRunningQ w h q c P S bs).1 = selectRunningQ w h q c P S bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons Bu bs ih =>
    obtain ⟨B, u⟩ := Bu
    simp only [countRunningQ, selectRunningQ]
    cases he : runningChoice w h q c P S B u <;> simp [he, ih]

private theorem countRunningQ_bound {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (S : ConditionalStats k) (bs : List (Finset (Fin m) × (Fin k → ℚ)))
    (hne : ∀ Bu ∈ bs, Bu.1.Nonempty) :
    (countRunningQ w h q c P S bs).2 ≤
      (26 * k + 1 + m.size) * (bs.map fun Bu => Bu.1.card).sum := by
  induction bs generalizing S with
  | nil => simp [countRunningQ]
  | cons Bu bs ih =>
    obtain ⟨B, u⟩ := Bu
    have htail : ∀ Bu ∈ bs, Bu.1.Nonempty := fun Bu hBu => hne Bu (List.mem_cons_of_mem _ hBu)
    have hpos : 0 < B.card := Finset.card_pos.mpr (hne (B,u) (by simp))
    have hm : B.card ≤ m := by simpa using B.card_le_univ
    have hb : runningTrialBudget k B.card + 10 * k ≤ (26 * k + 1 + m.size) * B.card := by
      have hsize := Nat.mul_le_mul_right B.card (Nat.size_le_size hm)
      have hsetup := Nat.mul_le_mul_left (22 * k) (show 1 ≤ B.card by omega)
      simp only [runningTrialBudget, indexSortBudget, Nat.add_mul, Nat.mul_one, Nat.mul_assoc, Nat.one_mul] at *
      omega
    simp only [countRunningQ, List.map_cons, List.sum_cons, Nat.mul_add]
    split
    · have hi := ih S htail
      omega
    · rename_i g _
      have hi := ih (replaceStats h u (fun t => w t g) S) htail
      omega

/-- One annotation pass and one initial summary plus the running selector. -/
def selectLinearCounted {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (buckets : List (Finset (Fin m))) : List (Fin m) × ℕ :=
  let annotated := buckets.map (fun B => (B, materialize (slotMeanQ w B)))
  let S := summarizeQ h (annotated.map Prod.snd)
  let out := countRunningQ w h q c P S annotated
  (out.1, k * (2 * candidateCount buckets + 6 * buckets.length + 2) + out.2)

theorem selectLinearCounted_result {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (buckets : List (Finset (Fin m))) :
    (selectLinearCounted w h q c P buckets).1 = selectLinearQ w h q c P [] buckets := by
  simp only [selectLinearCounted, countRunningQ_result, selectLinearQ, List.nil_append]

theorem selectLinearCounted_bound {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (buckets : List (Finset (Fin m)))
    (hne : ∀ B ∈ buckets, B.Nonempty) (hd : buckets.Pairwise Disjoint) :
    (selectLinearCounted w h q c P buckets).2 ≤
      36 * k * (m + 1) + m + indexSortBudget m := by
  let annotated := buckets.map (fun B => (B, materialize (slotMeanQ w B)))
  have he : (annotated.map fun Bu => Bu.1.card).sum = candidateCount buckets := by
    simp [annotated, candidateCount, List.map_map, Function.comp_def]
  have hb := countRunningQ_bound w h q c P (summarizeQ h (annotated.map Prod.snd)) annotated
    (fun Bu hBu => by
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hBu
      exact hne B hB)
  rw [he] at hb
  have hc := candidateCount_le_goods buckets hd
  have hlen := RationalAlgorithm1.length_le_candidateCount hne
  have hinit : k * (2 * candidateCount buckets + 6 * buckets.length + 2) ≤ k * (8 * m + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have htotal := Nat.mul_le_mul_left (26 * k + 1 + m.size) hc
  change _ + (countRunningQ w h q c P (summarizeQ h (annotated.map Prod.snd)) annotated).2 ≤ _
  calc
    _ ≤ k * (8 * m + 2) + (26 * k + 1 + m.size) * m :=
      Nat.add_le_add hinit (hb.trans htotal)
    _ ≤ _ := by
      unfold indexSortBudget
      nlinarith only [Nat.zero_le (k * m), Nat.zero_le k]

end OnlineMMS.BucketBitComplexity
