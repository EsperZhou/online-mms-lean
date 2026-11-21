import OnlineMMS.BucketLinearScores
import OnlineMMS.RationalAlgorithm1

namespace OnlineMMS.BucketBitComplexity

open RationalAlgorithm1 (materialize materialize_apply)

structure ConditionalStats (k : ℕ) where
  sums : Fin k → ℚ
  products : Fin k → ℚ

private def summarizeQ {k : ℕ} (h : ℚ) (slots : List (Fin k → ℚ)) : ConditionalStats k :=
  ⟨materialize fun t => (slots.map (fun z => z t)).sum,
    materialize fun t => sampleProductQ h (slots.map (fun z => z t))⟩

private def coefficientFromStats {k : ℕ} (h q c : ℚ) (P mean : Fin k → ℚ)
    (S : ConditionalStats k) (t : Fin k) : ℚ :=
  2 * q * (S.sums t - mean t) +
    c * (P t * S.products t / (1 + (h - 1) * mean t)) * (h - 1)

private def replaceStats {k : ℕ} (h : ℚ) (old fresh : Fin k → ℚ)
    (S : ConditionalStats k) : ConditionalStats k :=
  ⟨materialize fun t => S.sums t - old t + fresh t,
    materialize fun t =>
      S.products t / (1 + (h - 1) * old t) * (1 + (h - 1) * fresh t)⟩

private theorem replaceStats_summarize {k : ℕ} (h : ℚ)
    (left right : List (Fin k → ℚ)) (mean z : Fin k → ℚ)
    (hmean : ∀ t, 1 + (h - 1) * mean t ≠ 0) :
    replaceStats h mean z (summarizeQ h (left ++ mean :: right)) =
      summarizeQ h ((left ++ [z]) ++ right) := by
  have hs (t : Fin k) := replace_slot_statsQ h (mean t) (z t)
    (left.map (fun f => f t)) (right.map (fun f => f t)) (hmean t)
  unfold replaceStats summarizeQ
  congr 1
  · funext t
    simp only [materialize_apply, List.append_assoc, List.singleton_append, List.map_append,
      List.map_cons] at hs ⊢
    exact (hs t).1.symm
  · funext t
    simp only [materialize_apply, List.append_assoc, List.singleton_append, List.map_append,
      List.map_cons] at hs ⊢
    exact (hs t).2.symm

private theorem objectiveQ_fromStats {k : ℕ} (h q c : ℚ) (P mean z : Fin k → ℚ)
    (left right : List (Fin k → ℚ)) (hmean : ∀ t, 1 + (h - 1) * mean t ≠ 0) :
    objectiveQ h q c P (left ++ z :: right) =
      objectiveQ h q c P (left ++ (fun _ => 0) :: right) +
      ∑ t, z t * coefficientFromStats h q c P mean (summarizeQ h (left ++ mean :: right)) t := by
  rw [objectiveQ_slot]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  simpa [coefficientFromStats, summarizeQ] using
    slotCoefficientQ_of_totals h q c (P t) (mean t)
      (left.map (fun f => f t)) (right.map (fun f => f t)) (hmean t)

private theorem argmin_add_constant (L : List (Fin m)) (f g : Fin m → ℚ) (a : ℚ)
    (h : ∀ x, f x = a + g x) : L.argmin f = L.argmin g := by
  cases he : L.argmin g with
  | none =>
    rw [List.argmin_eq_none.mp he]
    rfl
  | some x =>
    obtain ⟨hx, hmin, htie⟩ := List.argmin_eq_some_iff.mp he
    apply List.argmin_eq_some_iff.mpr
    refine ⟨hx, fun y hy => ?_, fun y hy hle => ?_⟩
    · rw [h, h]
      exact add_le_add_left (hmin y hy) _
    · rw [h, h] at hle
      exact htie y hy (le_of_add_le_add_left hle)

/-- A cached coefficient column is shared by every comparison in the bucket. -/
private def runningChoice {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (S : ConditionalStats k) (B : Finset (Fin m)) (u : Fin k → ℚ) :
    Option (Fin m) :=
  let coef := materialize (coefficientFromStats h q c P u S)
  (B.sort (· ≤ ·)).argmin (fun g => ∑ t, w t g * coef t)

private def selectRunningQ {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ) :
    ConditionalStats k → List (Finset (Fin m) × (Fin k → ℚ)) → List (Fin m)
  | _, [] => []
  | S, (B, u) :: bs =>
    match runningChoice w h q c P S B u with
    | none => selectRunningQ w h q c P S bs
    | some g => g :: selectRunningQ w h q c P (replaceStats h u (fun t => w t g) S) bs

/-- Conditional sampling with retained sums and products. Means are tagged
once at initialization. -/
def selectLinearQ {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ)
    (left : List (Fin k → ℚ)) (buckets : List (Finset (Fin m))) : List (Fin m) :=
  let annotated := buckets.map (fun B => (B, materialize (slotMeanQ w B)))
  let S := summarizeQ h (left ++ annotated.map Prod.snd)
  selectRunningQ w h q c P S annotated

private theorem selectRunningQ_eq {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ)
    (hh : 1 ≤ h) (hw : ∀ t g, 0 ≤ w t g) (left : List (Fin k → ℚ))
    (buckets : List (Finset (Fin m))) (hne : ∀ B ∈ buckets, B.Nonempty) :
    selectRunningQ w h q c P (summarizeQ h (left ++ slotMeansQ w buckets))
      (buckets.map fun B => (B, slotMeanQ w B)) = selectQ w h q c P left buckets := by
  induction buckets generalizing left with
  | nil => rfl
  | cons B bs ih =>
    let u := slotMeanQ w B
    let right := slotMeansQ w bs
    let S := summarizeQ h (left ++ u :: right)
    let A (g : Fin m) := objectiveQ h q c P (left ++ (fun t => w t g) :: right)
    let C (g : Fin m) := ∑ t, w t g * materialize (coefficientFromStats h q c P u S) t
    have hf (t : Fin k) : 1 + (h - 1) * u t ≠ 0 := by
      have hu : 0 ≤ u t := div_nonneg (Finset.sum_nonneg fun g _ => hw t g) (by positivity)
      have hp := mul_nonneg (sub_nonneg.mpr hh) hu
      linarith
    have hcost : (B.sort (· ≤ ·)).argmin A = (B.sort (· ≤ ·)).argmin C := by
      apply argmin_add_constant _ _ _ (objectiveQ h q c P (left ++ (fun _ => 0) :: right))
      intro g
      simpa only [A, C, S, materialize_apply] using
        objectiveQ_fromStats h q c P u (fun t => w t g) left right hf
    unfold selectRunningQ selectQ runningChoice
    change (match (B.sort (· ≤ ·)).argmin C with
      | none => _
      | some g => g :: selectRunningQ w h q c P (replaceStats h u (fun t => w t g) S)
          (bs.map fun B => (B, slotMeanQ w B))) =
      (match (B.sort (· ≤ ·)).argmin A with
      | none => _
      | some g => g :: selectQ w h q c P (left ++ [fun t => w t g]) bs)
    rw [hcost]
    cases he : (B.sort (· ≤ ·)).argmin C with
    | none =>
      have hm : (B.sort (· ≤ ·)).length = 0 := by rw [List.argmin_eq_none.mp he]; rfl
      rw [Finset.length_sort] at hm
      exact (Nat.ne_of_gt (Finset.card_pos.mpr (hne B (by simp))) hm).elim
    | some g =>
      have hr : ∀ D ∈ bs, D.Nonempty := fun D hD => hne D (by simp [hD])
      simp only
      congr 1
      rw [show replaceStats h u (fun t => w t g) S =
        summarizeQ h ((left ++ [fun t => w t g]) ++ right) from
        replaceStats_summarize h left right u _ hf]
      exact ih _ hr

/-- The optimized selector makes exactly the same choices as the verified
recomputation selector, including its fixed tie order. -/
theorem selectLinearQ_eq {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ)
    (hh : 1 ≤ h) (hw : ∀ t g, 0 ≤ w t g) (left : List (Fin k → ℚ))
    (buckets : List (Finset (Fin m))) (hne : ∀ B ∈ buckets, B.Nonempty) :
    selectLinearQ w h q c P left buckets = selectQ w h q c P left buckets := by
  have he (B : Finset (Fin m)) : materialize (slotMeanQ w B) = slotMeanQ w B :=
    funext (materialize_apply _)
  unfold selectLinearQ
  simp only [he, List.map_map, Function.comp_def]
  exact selectRunningQ_eq w h q c P hh hw left buckets hne

end OnlineMMS.BucketBitComplexity
