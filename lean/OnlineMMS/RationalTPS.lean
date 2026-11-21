import OnlineMMS.Benchmarks
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.Order

namespace OnlineMMS

/-- Candidate intersection for the interval immediately to the right
of the given breakpoint. A denominator of zero gives a dummy candidate. -/
def rationalTPSIntersection {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (breakpoint : ℚ) : ℚ :=
  (∑ g ∈ Finset.univ.filter (fun g => v g ≤ breakpoint), v g) /
    (n - (Finset.univ.filter (fun g => breakpoint < v g)).card : ℕ)

def rationalTPSCandidates {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : Finset ℚ :=
  insert 0 ((insert 0 (Finset.univ.image v)).image (rationalTPSIntersection v n))

def rationalTPSFeasible {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (q : ℚ) : Prop :=
  0 ≤ q ∧ (n : ℚ) * q ≤ ∑ g, min (v g) q

instance {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (q : ℚ) :
    Decidable (rationalTPSFeasible v n q) := by
  unfold rationalTPSFeasible
  infer_instance

/-- An executable scan using at most m+2 candidate values. -/
def rationalTPS {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : ℚ :=
  (insert 0 ((rationalTPSCandidates v n).filter (rationalTPSFeasible v n))).max'
    (Finset.insert_nonempty _ _)

theorem rationalTPSCandidates_card {m : ℕ} (v : Fin m → ℚ) (n : ℕ) :
    (rationalTPSCandidates v n).card ≤ m + 2 := by
  unfold rationalTPSCandidates
  calc
    _ ≤ ((insert 0 (Finset.univ.image v)).image (rationalTPSIntersection v n)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (insert 0 (Finset.univ.image v)).card + 1 := Nat.add_le_add_right Finset.card_image_le _
    _ ≤ (Finset.univ.image v).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
    _ ≤ m + 2 := by
      have h : (Finset.univ.image v).card ≤ m := Finset.card_image_le.trans_eq (by simp)
      omega

private theorem rationalTPSFeasible_cast {m n : ℕ} {v : Fin m → ℚ} {q : ℚ} :
    rationalTPSFeasible v n q ↔ (q : ℝ) ∈ tpsFeasible (fun g => (v g : ℝ)) n := by
  unfold rationalTPSFeasible
  change _ ↔ 0 ≤ (q : ℝ) ∧ (n : ℝ) * q ≤ ∑ g, min (v g : ℝ) (q : ℝ)
  exact_mod_cast Iff.rfl

private theorem tps_high_count {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ} (hv : ∀ g, 0 ≤ v g) :
    (Finset.univ.filter (fun g => truncatedShare v n < v g)).card < n := by
  classical
  let d := truncatedShare v n
  let high := Finset.univ.filter (fun g => d < v g)
  change high.card < n
  apply lt_of_not_ge
  intro hc
  have hne : high.Nonempty := Finset.card_pos.mp (hn.trans_le hc)
  obtain ⟨g, hg, hmin⟩ := high.exists_min_image v hne
  have hdg : d < v g := (Finset.mem_filter.mp hg).2
  have hspec := truncatedShare_spec v hv hn
  have hq : v g ∈ tpsFeasible v n := by
    refine ⟨hv g, ?_⟩
    calc
      (n : ℝ) * v g ≤ (high.card : ℝ) * v g :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hv g)
      _ = ∑ _i ∈ high, v g := by simp [nsmul_eq_mul]
      _ = ∑ i ∈ high, min (v i) (v g) :=
        Finset.sum_congr rfl fun i hi => (min_eq_right (hmin i hi)).symm
      _ ≤ ∑ i, min (v i) (v g) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => le_min (hv i) (hv g))
  exact (not_le_of_gt hdg) (hspec.2 hq)

/-- This candidate set contains the exact real TPS, even though it is
computed solely with rational comparisons and arithmetic. -/
theorem rationalTPSCandidates_complete {m n : ℕ} (hn : 0 < n)
    (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) :
    ∃ q ∈ rationalTPSCandidates v n, (q : ℝ) = truncatedShare (fun g => (v g : ℝ)) n := by
  classical
  let w : Fin m → ℝ := fun g => v g
  let d := truncatedShare w n
  have hw (g : Fin m) : 0 ≤ w g := by
    dsimp [w]
    exact_mod_cast hv g
  have hspec := truncatedShare_spec w hw hn
  change ∃ q ∈ rationalTPSCandidates v n, (q : ℝ) = d
  by_cases hz : d = 0
  · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hz.symm⟩
  have hd : 0 < d := lt_of_le_of_ne hspec.1.1 (Ne.symm hz)
  let low := Finset.univ.filter (fun g => w g ≤ d)
  let high := Finset.univ.filter (fun g => d < w g)
  have hcount : high.card < n := tps_high_count hn hw
  have hsplit : ∑ g, min (w g) d = (∑ g ∈ low, w g) + (high.card : ℝ) * d := by
    calc
      ∑ g, min (w g) d = (∑ g ∈ low, w g) + ∑ _g ∈ high, d := by
        dsimp [low, high]
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro g _
        by_cases h : w g ≤ d
        · simp [h, min_eq_left h, not_lt_of_ge h]
        · have hh := lt_of_not_ge h
          simp [h, hh, min_eq_right hh.le]
      _ = _ := by simp [nsmul_eq_mul]
  have hs := truncatedShare_saturates w hw hn
  change ∑ g, min (w g) d = (n : ℝ) * d at hs
  rw [hsplit] at hs
  have hpos : 0 < (n - high.card : ℕ) := by omega
  have hcaR : (high.card : ℝ) < n := by exact_mod_cast hcount
  have hnonempty : low.Nonempty := by
    by_cases he : low = ∅
    · rw [he, Finset.sum_empty, zero_add] at hs
      exact False.elim ((ne_of_lt (mul_lt_mul_of_pos_right hcaR hd)) hs)
    · exact Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨i, hi, hmax⟩ := low.exists_max_image w hnonempty
  have hiD : w i ≤ d := (Finset.mem_filter.mp hi).2
  have hlow : Finset.univ.filter (fun g => v g ≤ v i) = low := by
    ext g
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hg
      exact (show w g ≤ w i by dsimp [w]; exact_mod_cast hg).trans hiD
    · intro hg
      have hh := hmax g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
      dsimp [w] at hh
      exact_mod_cast hh
  have hhigh : Finset.univ.filter (fun g => v i < v g) = high := by
    ext g
    have he := Finset.ext_iff.mp hlow g
    simpa [high, low, not_le] using not_congr he
  let q := rationalTPSIntersection v n (v i)
  refine ⟨q, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v i,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), rfl⟩), ?_⟩
  unfold q rationalTPSIntersection
  rw [hlow, hhigh]
  push_cast
  apply (div_eq_iff (by exact_mod_cast (Nat.ne_of_gt hpos))).mpr
  rw [Nat.cast_sub hcount.le]
  change (∑ g ∈ low, w g) = _
  linarith only [hs]

/-- The rational candidate scan exactly computes the original real TPS. -/
theorem rationalTPS_correct {m n : ℕ} (hn : 0 < n) (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) :
    (rationalTPS v n : ℝ) = truncatedShare (fun g => (v g : ℝ)) n := by
  let q := rationalTPS v n
  let w : Fin m → ℝ := fun g => v g
  have hw (g : Fin m) : 0 ≤ w g := by
    dsimp [w]
    exact_mod_cast hv g
  have hspec := truncatedShare_spec w hw hn
  obtain ⟨q', hq', he⟩ := rationalTPSCandidates_complete hn v hv
  have hqf : rationalTPSFeasible v n q' := rationalTPSFeasible_cast.mpr (he ▸ hspec.1)
  have hlow : (q' : ℝ) ≤ q := by
    exact_mod_cast Finset.le_max' _ q' (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hq', hqf⟩))
  have hqMem := Finset.max'_mem (insert 0 ((rationalTPSCandidates v n).filter
    (rationalTPSFeasible v n))) (Finset.insert_nonempty _ _)
  change q ∈ insert 0 ((rationalTPSCandidates v n).filter (rationalTPSFeasible v n)) at hqMem
  have hupper : (q : ℝ) ≤ truncatedShare w n := by
    rcases Finset.mem_insert.mp hqMem with hzero | hmem
    · simpa [hzero] using hspec.1.1
    · exact hspec.2 (rationalTPSFeasible_cast.mp (Finset.mem_filter.mp hmem).2)
  exact le_antisymm hupper (he ▸ hlow)

/-- After clearing input denominators by D, a positive TPS is A/(D B).
A is a subsum of the scaled input and B is at most the horizon. -/
theorem rationalTPS_scaled_fraction {m n D : ℕ} (_hn : 0 < n) (_hD : 0 < D)
    (a : Fin m → ℕ) :
    let v : Fin m → ℚ := fun g => (a g : ℚ) / D
    0 < rationalTPS v n →
    ∃ A B : ℕ, A ≤ ∑ g, a g ∧ 0 < A ∧ 0 < B ∧ B ≤ n ∧
      rationalTPS v n = (A : ℚ) / (D * B : ℕ) := by
  classical
  let v : Fin m → ℚ := fun g => (a g : ℚ) / D
  change 0 < rationalTPS v n → _
  intro hpos
  have hqMem := Finset.max'_mem (insert 0 ((rationalTPSCandidates v n).filter
    (rationalTPSFeasible v n))) (Finset.insert_nonempty _ _)
  change rationalTPS v n ∈ insert 0 ((rationalTPSCandidates v n).filter
    (rationalTPSFeasible v n)) at hqMem
  have hcan := (Finset.mem_filter.mp ((Finset.mem_insert.mp hqMem).resolve_left hpos.ne')).1
  have hmem := (Finset.mem_insert.mp hcan).resolve_left hpos.ne'
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
  let S := Finset.univ.filter (fun g => v g ≤ q)
  let A := ∑ g ∈ S, a g
  let B := n - (Finset.univ.filter (fun g => q < v g)).card
  have he : rationalTPS v n = (A : ℚ) / (D * B : ℕ) := by
    rw [← hq]
    change (∑ g ∈ S, (a g : ℚ) / D) / (B : ℚ) = _
    rw [← Finset.sum_div, ← Nat.cast_sum, div_div, Nat.cast_mul]
  have hA : 0 < A := by
    by_contra! h
    have hz : A = 0 := by omega
    simp [he, hz] at hpos
  have hB : 0 < B := by
    by_contra! h
    have hz : B = 0 := by omega
    simp [he, hz] at hpos
  exact ⟨A, B, Finset.sum_le_sum_of_subset (Finset.subset_univ _), hA, hB, Nat.sub_le _ _, he⟩

/-- Initial capped normalized weights share a denominator bounded by the
sum of the scaled integer item values. -/
theorem rationalTPS_normalized_common_denominator {m n D : ℕ} (hn : 0 < n) (hD : 0 < D)
    (a : Fin m → ℕ) :
    let v : Fin m → ℚ := fun g => (a g : ℚ) / D
    let w : Fin m → ℝ := fun g => v g
    0 < truncatedShare w n →
    ∃ A : ℕ, 0 < A ∧ A ≤ ∑ g, a g ∧
      ∀ g, ∃ u ≤ A, normalizedWeight w n g = (u : ℝ) / A := by
  classical
  let v : Fin m → ℚ := fun g => (a g : ℚ) / D
  let w : Fin m → ℝ := fun g => v g
  change 0 < truncatedShare w n → _
  intro hd
  have hv (g : Fin m) : 0 ≤ v g := by dsimp [v]; positivity
  have hq := rationalTPS_correct hn v hv
  have hpos : 0 < rationalTPS v n := by
    have h : (0 : ℝ) < (rationalTPS v n : ℝ) := hq ▸ hd
    exact_mod_cast h
  obtain ⟨A, B, hA, hpA, hpB, _, hf⟩ := rationalTPS_scaled_fraction hn hD a hpos
  have hdForm : truncatedShare w n = (A : ℝ) / ((D : ℝ) * (B : ℝ)) := by
    rw [← hq, hf]
    push_cast
    rfl
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpB)
  have hA' : 0 < (A : ℝ) := by exact_mod_cast hpA
  refine ⟨A, hpA, hA, fun g => ⟨min A (a g * B), min_le_left _ _, ?_⟩⟩
  rw [normalizedWeight_eq w hd g, hdForm]
  have hw : w g = (a g : ℝ) / D := by
    dsimp [w, v]
    push_cast
    rfl
  rw [hw, show ((a g : ℝ) / D) / ((A : ℝ) / (D * B)) = (a g : ℝ) * B / A by
    field_simp [hD', hB', hA'.ne']
    ring]
  rw [Nat.cast_min, Nat.cast_mul, ← min_div_div_right hA'.le, div_self hA'.ne']

end OnlineMMS
