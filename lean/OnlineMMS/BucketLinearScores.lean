import OnlineMMS.BucketSelectorCost

namespace OnlineMMS.BucketBitComplexity

/-- Rational form of the exact linear coefficient of a single bucket. -/
def slotCoefficientQ (h q c p : ℚ) (left right : List ℚ) : ℚ :=
  2 * q * (left.sum + right.sum) +
    c * p * sampleProductQ h left * sampleProductQ h right * (h - 1)

theorem slotCoefficientQ_cast (h q c p : ℚ) (left right : List ℚ) :
    (slotCoefficientQ h q c p left right : ℝ) =
      slotCoefficient h q c p (left.map (fun z : ℚ => (z : ℝ)))
        (right.map (fun z : ℚ => (z : ℝ))) := by
  simp only [slotCoefficientQ, slotCoefficient, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_list_sum, sampleProductQ_cast]

private theorem pairSumQ_append (left right : List ℚ) :
    pairSumQ (left ++ right) = pairSumQ left + pairSumQ right + left.sum * right.sum := by
  induction left with
  | nil => simp [pairSumQ]
  | cons x xs ih =>
    simp only [List.cons_append, pairSumQ, List.sum_cons, List.sum_append, ih]
    ring

theorem rowObjectiveQ_slot (h q c p x : ℚ) (left right : List ℚ) :
    rowObjectiveQ h q c p (left ++ x :: right) =
      rowObjectiveQ h q c p (left ++ 0 :: right) + x * slotCoefficientQ h q c p left right := by
  simp only [rowObjectiveQ, slotCoefficientQ, pairSumQ_append, pairSumQ, List.sum_cons,
    sampleProductQ, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

theorem objectiveQ_slot {k : ℕ} (h q c : ℚ) (P z : Fin k → ℚ)
    (left right : List (Fin k → ℚ)) :
    objectiveQ h q c P (left ++ z :: right) =
      objectiveQ h q c P (left ++ (fun _ => 0) :: right) +
      ∑ t, z t * slotCoefficientQ h q c (P t)
        (left.map (fun p => p t)) (right.map (fun p => p t)) := by
  unfold objectiveQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [List.map_append, List.map_cons] using
    rowObjectiveQ_slot h q c (P t) (z t) (left.map (fun p => p t)) (right.map (fun p => p t))

private theorem sampleProductQ_slot (h : ℚ) (left right : List ℚ) (x : ℚ) :
    sampleProductQ h (left ++ x :: right) =
      sampleProductQ h left * sampleProductQ h right * (1 + (h - 1) * x) := by
  simp only [sampleProductQ, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

/-- The coefficient can use the retained total sum and the retained
conditional product. The current slot factor is divided out exactly. -/
theorem slotCoefficientQ_of_totals (h q c p u : ℚ) (left right : List ℚ)
    (hfactor : 1 + (h - 1) * u ≠ 0) :
    slotCoefficientQ h q c p left right =
      2 * q * ((left ++ u :: right).sum - u) +
      c * (p * sampleProductQ h (left ++ u :: right) / (1 + (h - 1) * u)) * (h - 1) := by
  rw [sampleProductQ_slot]
  unfold slotCoefficientQ
  rw [List.sum_append, List.sum_cons]
  field_simp [hfactor]
  ring

/-- Updating the retained sum and product requires one subtraction and
addition and one replacement of the slot factor. -/
theorem replace_slot_statsQ (h u x : ℚ) (left right : List ℚ)
    (hfactor : 1 + (h - 1) * u ≠ 0) :
    (left ++ x :: right).sum = (left ++ u :: right).sum - u + x ∧
    sampleProductQ h (left ++ x :: right) =
      sampleProductQ h (left ++ u :: right) / (1 + (h - 1) * u) * (1 + (h - 1) * x) := by
  constructor
  · simp only [List.sum_append, List.sum_cons]
    ring
  · rw [sampleProductQ_slot h left right x, sampleProductQ_slot h left right u]
    field_simp [hfactor]

/-- The local coefficient and candidate-evaluation budget is linear in the
sum of bucket sizes, including one coefficient update per nonempty bucket. -/
theorem linearBucketWork_le {m : ℕ} (k setup perGood : ℕ)
    (buckets : List (Finset (Fin m))) (hne : ∀ B ∈ buckets, B.Nonempty)
    (hd : buckets.Pairwise Disjoint) :
    ((buckets.map (fun B => k * (setup + perGood * B.card))).sum) ≤
      k * (setup + perGood) * m := by
  have hC := candidateCount_le_goods buckets hd
  have hlocal (B : Finset (Fin m)) (hB : B ∈ buckets) :
      k * (setup + perGood * B.card) ≤ (k * (setup + perGood)) * B.card := by
    have hp : 1 ≤ B.card := Finset.card_pos.mpr (hne B hB)
    calc
      _ ≤ k * (setup * B.card + perGood * B.card) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right
          (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left setup hp) _)
      _ = _ := by ring
  have hsum : ∀ (bs : List (Finset (Fin m))),
      (∀ B ∈ bs, B ∈ buckets) →
      (bs.map (fun B => k * (setup + perGood * B.card))).sum ≤
        (k * (setup + perGood)) * candidateCount bs := by
    intro bs hb
    induction bs with
    | nil => simp [candidateCount]
    | cons B rest ih =>
      have ih' := ih (fun C hC => hb C (by simp [hC]))
      have hB := hlocal B (hb B (by simp))
      simp only [List.map_cons, List.sum_cons, candidateCount, Nat.mul_add] at *
      exact Nat.add_le_add hB ih'
  exact (hsum buckets (fun _ h => h)).trans (Nat.mul_le_mul_left _ hC)

end OnlineMMS.BucketBitComplexity
