import OnlineMMS.RationalTPS
import OnlineMMS.MergeSortCost

namespace OnlineMMS

open private tps_high_count from OnlineMMS.RationalTPS

/-- The sorted sweep maintains the sum of the processed items and the exact size
of the suffix. Its interval intersection is tested against the next item. -/
def tpsSweep {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : ℕ → ℚ → List (Fin m) → ℚ
  | _, A, [] => A / n
  | c, A, g :: gs =>
    if c < n then
      let y : ℚ := A / (n - c : ℕ)
      if y ≤ v g then y else tpsSweep v n (c - 1) (A + v g) gs
    else tpsSweep v n (c - 1) (A + v g) gs

private theorem cap_sum_le {m : ℕ} (v : Fin m → ℝ) (d : ℝ) (tail : List (Fin m)) :
    (tail.map (fun g => min (v g) d)).sum ≤ (tail.length : ℝ) * d := by
  induction tail with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    linarith [min_le_right (v g) d]

private theorem tpsSweep_correct {m n : ℕ} (hn : 0 < n)
    (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) :
    let w : Fin m → ℝ := fun g => v g
    let d := truncatedShare w n
    ∀ (tail doneGoods : List (Fin m)),
      (doneGoods ++ tail).Perm (List.finRange m) →
      (∀ g ∈ doneGoods, w g ≤ d) →
      tail.Pairwise (fun g g' => v g ≤ v g') →
      (tpsSweep v n tail.length (doneGoods.map v).sum tail : ℝ) = d := by
  classical
  let w : Fin m → ℝ := fun g => v g
  let d := truncatedShare w n
  have hw (g : Fin m) : 0 ≤ w g := by dsimp [w]; exact_mod_cast hv g
  have hsat := truncatedShare_saturates w hw hn
  have hhigh := tps_high_count hn hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass {p s : List (Fin m)} (hperm : (p ++ s).Perm (List.finRange m))
      (hle : ∀ g ∈ p, w g ≤ d) :
      ((p.map v).sum : ℝ) + (s.map (fun g => min (w g) d)).sum = (n : ℝ) * d := by
    have he := (hperm.map (fun g => min (w g) d)).sum_eq
    have hs : ((List.finRange m).map (fun g => min (w g) d)).sum = ∑ g, min (w g) d := by
      simpa only [List.toFinset_finRange] using
        (List.sum_toFinset (fun g => min (w g) d) (List.nodup_finRange m)).symm
    rw [hs, hsat, List.map_append, List.sum_append] at he
    rw [Rat.cast_list_sum, show (List.map (fun q : ℚ => (q : ℝ)) (p.map v)) =
      p.map (fun g => min (w g) d) by
        rw [List.map_map]
        apply List.map_congr_left
        intro g hg
        exact (min_eq_left (hle _ hg)).symm]
    exact he
  change ∀ (tail doneGoods : List (Fin m)),
    (doneGoods ++ tail).Perm (List.finRange m) →
    (∀ g ∈ doneGoods, w g ≤ d) →
    tail.Pairwise (fun g g' => v g ≤ v g') →
    (tpsSweep v n tail.length (doneGoods.map v).sum tail : ℝ) = d
  intro tail
  induction tail with
  | nil =>
    intro doneGoods hp hle _
    have hm := hmass hp hle
    simp only [List.map_nil, List.sum_nil, add_zero] at hm
    simp only [tpsSweep, Rat.cast_div, Rat.cast_natCast]
    exact (div_eq_iff hnR.ne').mpr (by linarith)
  | cons g gs ih =>
    intro doneGoods hp hle hs
    let tail := g :: gs
    let A := (doneGoods.map v).sum
    let c := tail.length
    have hmass0 := hmass hp hle
    have htail (hh : d ≤ w g) :
        (tail.map (fun i => min (w i) d)).sum = (c : ℝ) * d := by
      have hmin (i : Fin m) (hi : i ∈ tail) : min (w i) d = d := by
        apply min_eq_right
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hh
        · exact hh.trans (show w g ≤ w i by
            dsimp [w]; exact_mod_cast ((List.pairwise_cons.mp hs).1 i hi))
      have he : tail.map (fun i => min (w i) d) = tail.map (fun _ => d) :=
        List.map_congr_left hmin
      rw [he]
      have ht (ls : List (Fin m)) : (ls.map (fun _ => d)).sum = (ls.length : ℝ) * d := by
        induction ls with
        | nil => simp
        | cons _ xs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]
          ring
      exact ht tail
    have hless (h : w g ≤ d) :
        (tpsSweep v n gs.length ((doneGoods.map v).sum + v g) gs : ℝ) = d := by
      have hnext := ih (doneGoods ++ [g]) (by simpa only [List.append_assoc, List.singleton_append] using hp)
        (fun i hi => by
          rcases List.mem_append.mp hi with hi | hi
          · exact hle _ hi
          · rwa [List.mem_singleton.mp hi])
        hs.of_cons
      simpa only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero] using hnext
    have hc_tail : c - 1 = gs.length := by simp [c, tail]
    have hcSmall (hdg : w g > d) : c < n := by
      have hnodup : tail.Nodup := by
        have hu := hp.nodup_iff.mpr (List.nodup_finRange m)
        exact (List.nodup_append.mp hu).2.1
      have hsub : tail.toFinset ⊆ Finset.univ.filter (fun i => d < w i) := by
        intro i hi
        have hmem := List.mem_toFinset.mp hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hdg
        · exact hdg.trans_le (show w g ≤ w i by
            dsimp [w]; exact_mod_cast ((List.pairwise_cons.mp hs).1 i hmem))
      have he : tail.toFinset.card = c := List.toFinset_card_of_nodup hnodup
      rw [← he]
      exact (Finset.card_le_card hsub).trans_lt hhigh
    change (tpsSweep v n c A tail : ℝ) = d
    rw [tpsSweep]
    change (↑(if c < n then
        if A / (n - c : ℕ) ≤ v g then A / (n - c : ℕ)
        else tpsSweep v n (c - 1) (A + v g) gs
      else tpsSweep v n (c - 1) (A + v g) gs) : ℝ) = d
    by_cases hc : c < n
    · rw [if_pos hc]
      let y : ℚ := A / (n - c : ℕ)
      have hden : (0 : ℝ) < (n : ℝ) - c := sub_pos.mpr (by exact_mod_cast hc)
      have hy : (y : ℝ) = (A : ℝ) / ((n : ℝ) - c) := by
        simp [y, Rat.cast_div, Nat.cast_sub hc.le]
      have hdY : d ≤ (y : ℝ) := by
        rw [hy, le_div_iff₀ hden]
        have ht := cap_sum_le w d tail
        change (A : ℝ) + (tail.map (fun i => min (w i) d)).sum = (n : ℝ) * d at hmass0
        change (tail.map (fun i => min (w i) d)).sum ≤ (c : ℝ) * d at ht
        nlinarith only [ht, hmass0]
      have hdEq (hdg : d ≤ w g) : (y : ℝ) = d := by
        rw [hy, div_eq_iff hden.ne']
        change (A : ℝ) + (tail.map (fun i => min (w i) d)).sum = (n : ℝ) * d at hmass0
        rw [htail hdg] at hmass0
        nlinarith only [hmass0]
      by_cases hfit : y ≤ v g
      · rw [if_pos hfit]
        exact hdEq (hdY.trans (show (y : ℝ) ≤ w g by dsimp [w]; exact_mod_cast hfit))
      · rw [if_neg hfit, hc_tail]
        apply hless
        apply le_of_not_gt
        intro hdg
        have he := hdEq hdg.le
        have hyR : w g < (y : ℝ) := by dsimp [w]; exact_mod_cast (lt_of_not_ge hfit)
        linarith
    · rw [if_neg hc, hc_tail]
      exact hless (le_of_not_gt (fun h => hc (hcSmall h)))

/-- Ascending merge sort followed by the executable one-pass TPS sweep. -/
def rationalTPSFast {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : ℚ :=
  tpsSweep v n m 0 ((List.finRange m).mergeSort (fun g g' => decide (v g ≤ v g')))

theorem rationalTPSFast_correct {m n : ℕ} (hn : 0 < n)
    (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) :
    (rationalTPSFast v n : ℝ) = truncatedShare (fun g => (v g : ℝ)) n := by
  let rel (g g' : Fin m) := v g ≤ v g'
  letI : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
  letI : IsTotal (Fin m) rel := ⟨fun g g' => le_total (v g) (v g')⟩
  letI : IsTrans (Fin m) rel := ⟨fun _ _ _ => le_trans⟩
  let goods := (List.finRange m).mergeSort (fun g g' => decide (rel g g'))
  have hperm : goods.Perm (List.finRange m) := List.mergeSort_perm _ _
  have hsorted : goods.Pairwise rel := List.sorted_mergeSort' rel _
  have hlen : goods.length = m := by simp [goods]
  have h := tpsSweep_correct hn v hv goods [] (by simpa using hperm) (by simp) hsorted
  simpa [rationalTPSFast, goods, rel, hlen] using h

theorem rationalTPSFast_eq {m n : ℕ} (hn : 0 < n)
    (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) : rationalTPSFast v n = rationalTPS v n := by
  apply Rat.cast_injective (α := ℝ)
  exact (rationalTPSFast_correct hn v hv).trans (rationalTPS_correct hn v hv).symm

private def tpsSweepVisits {m : ℕ} (v : Fin m → ℚ) (n : ℕ) :
    ℕ → ℚ → List (Fin m) → ℕ
  | _, _, [] => 1
  | c, A, g :: gs =>
    if c < n then
      if A / (n - c : ℕ) ≤ v g then 5
      else 6 + tpsSweepVisits v n (c - 1) (A + v g) gs
    else 6 + tpsSweepVisits v n (c - 1) (A + v g) gs

private theorem tpsSweepVisits_le {m : ℕ} (v : Fin m → ℚ) (n c : ℕ) (A : ℚ)
    (goods : List (Fin m)) : tpsSweepVisits v n c A goods ≤ 6 * (goods.length + 1) := by
  induction goods generalizing c A with
  | nil => simp [tpsSweepVisits]
  | cons g gs ih =>
    have h := ih (c - 1) (A + v g)
    unfold tpsSweepVisits
    split <;> first | split <;> simp only [List.length_cons] <;> omega | simp only [List.length_cons]; omega

/-- The sorted scan uses the original logarithmic comparison bound and
one constant-sized arithmetic batch per input good. -/
theorem rationalTPSFast_work_le {m : ℕ} (v : Fin m → ℚ) (n : ℕ) :
    let leQ := fun g g' => decide (v g ≤ v g')
    mergeSortComparisons leQ (List.finRange m) +
      tpsSweepVisits v n m 0 ((List.finRange m).mergeSort leQ) ≤
      m.size * m + 6 * (m + 1) := by
  dsimp only
  apply Nat.add_le_add
  · simpa using mergeSortComparisons_le (fun g g' => decide (v g ≤ v g')) (List.finRange m)
  · simpa using tpsSweepVisits_le v n m 0 ((List.finRange m).mergeSort (fun g g' => decide (v g ≤ v g')))

end OnlineMMS
