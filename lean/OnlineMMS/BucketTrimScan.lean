import OnlineMMS.BucketBitComplexity

namespace OnlineMMS.BucketBitComplexity

/-- Visit each retained good once, writing its trimmed weight into a
materialized row. The original row is used throughout the scan. -/
private def trimScan {m : ℕ} (w : Fin m → ℚ) :
    List (Fin m) → ℚ → Vector ℚ m → Vector ℚ m
  | [], _, output => output
  | g :: gs, remove, output =>
    trimScan w gs (max 0 (remove - w g)) (output.set g.val (max 0 (w g - remove)) g.isLt)

private theorem trimScan_get {m : ℕ} (w : Fin m → ℚ) (gs : List (Fin m))
    (hn : gs.Nodup) (remove : ℚ) (output : Vector ℚ m) (x : Fin m) :
    (trimScan w gs remove output).get x =
      if x ∈ gs then trimListQ w gs remove x else output.get x := by
  induction gs generalizing remove output with
  | nil => simp [trimScan]
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := List.nodup_cons.mp hn
    rw [trimScan, ih hgs]
    by_cases hx : x = g
    · subst x
      simp [hg, trimListQ, Vector.get]
    · by_cases hm : x ∈ gs
      · simp [hx, hm, trimListQ]
      · have hval : x.val ≠ g.val := fun he => hx (Fin.ext he)
        have hne : g.val ≠ x.val := Ne.symm hval
        simp [hx, hm, Vector.get, hne, hval]

/-- Apply the trim to a list sorted once for all valuation rows. -/
def trimWeightsOrdered {m : ℕ} (remaining : Finset (Fin m)) (ordered : List (Fin m))
    (w : Fin m → ℚ) (cap : ℚ) : Vector ℚ m :=
  trimScan w ordered (max 0 ((∑ g ∈ remaining, w g) - cap)) (Vector.replicate m 0)

def trimWeightsVector {m : ℕ} (remaining : Finset (Fin m)) (w : Fin m → ℚ)
    (cap : ℚ) : Vector ℚ m :=
  trimWeightsOrdered remaining (remaining.sort (· ≤ ·)) w cap

@[simp] theorem trimWeightsVector_get {m : ℕ} (remaining : Finset (Fin m)) (w : Fin m → ℚ)
    (cap : ℚ) (x : Fin m) :
    (trimWeightsVector remaining w cap).get x = trimWeightsQ remaining w cap x := by
  have hone (gs : List (Fin m)) (h : x ∉ gs) (rem : ℚ) : trimListQ w gs rem x = 0 := by
    induction gs generalizing rem with
    | nil => rfl
    | cons g gs ih =>
      have hne : x ≠ g := fun he => h (by simp [he])
      have ht : x ∉ gs := fun hg => h (List.mem_cons_of_mem _ hg)
      simp [trimListQ, hne, ih ht]
  unfold trimWeightsVector trimWeightsOrdered trimWeightsQ
  rw [trimScan_get w _ (Finset.sort_nodup _ _)]
  split
  · rfl
  · rename_i h
    rw [hone _ h _]
    simp [Vector.get]

/-- Writes and rational updates in the scan, one fixed batch per retained
good. The initial sum and the zero row have linear length as well. -/
theorem trim_scan_work_le {m : ℕ} (R : Finset (Fin m)) :
    m + R.card + 4 * (R.sort (· ≤ ·)).length + 3 ≤ 6 * (m + 1) := by
  rw [Finset.length_sort]
  have h : R.card ≤ m := by simpa using R.card_le_univ
  omega

end OnlineMMS.BucketBitComplexity
