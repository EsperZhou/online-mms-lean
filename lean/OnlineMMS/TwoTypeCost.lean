import OnlineMMS.TwoTypeRationalPolicy
import OnlineMMS.RationalArithmetic

namespace OnlineMMS.TwoType

open RationalArithmetic

/-- Count the level tests in a full scan of all feasible-scale candidates.
The bound includes the tests for zero and the two endpoints. -/
def scoreScanTests {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (a : ℚ) : ℕ :=
  let L := scaleScanLimit v
  let U := (∑ g, v g) / (n : ℚ)
  (scaleCandidatesRat v a U L).card * m * (boundedLevels L).length

theorem scoreScanTests_le {m : ℕ} (v : Fin m → ℚ) (n : ℕ) (a : ℚ) :
    scoreScanTests v n a ≤
      (2 * m * (2 * valuationDigits v + m) + 2) * m * (2 * (2 * valuationDigits v + m) + 2) := by
  unfold scoreScanTests
  dsimp only
  rw [boundedLevels_length]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (scaleCandidatesRat_card ..))

/-- Number of pair/triple carries in the actual preprocessing of a menu. -/
theorem preparedMenu_merges_le_goods {m : ℕ} (tag : Fin m → Option PacketLevel)
    (w : Fin m → ℝ) (R : Finset (Fin m))
    (hw : ∀ g, w g = (tag g).elim 0 PacketLevel.weight) :
    let P := initialPackets tag R
    (normalizePackets P.length P).2 ≤ R.card := by
  obtain ⟨hnd, hv, _, _⟩ := initialPackets_spec tag R w hw
  let P := initialPackets tag R
  have h := normalizePackets_spec P.length P hnd hv le_rfl
  change (normalizePackets P.length P).2 ≤ R.card
  rcases he : normalizePackets P.length P with ⟨Q, count⟩
  rw [he] at h
  exact (Nat.le_add_right count Q.length).trans (h.2.2.2.2.trans (initialPackets_length tag R))

private theorem valuation_bounded {m : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) (g : Fin m) :
    Bounded (v g) (valuationDigits v) := by
  have hh : (v g).num.natAbs.size + (v g).den.size ≤ valuationDigits v := by
    unfold valuationDigits
    exact Finset.single_le_sum (fun i _ => Nat.zero_le
      ((v i).num.natAbs.size + (v i).den.size)) (Finset.mem_univ g)
  refine ⟨(v g).num.natAbs, (v g).den, (v g).pos, ?_, Nat.size_le.mp (by omega), Nat.size_le.mp (by omega)⟩
  have he := congrArg (fun b : ℤ => (b : ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hv g)))
  exact (Rat.num_div_den (v g)).symm.trans
    (congrArg (fun b : ℚ => b / (v g).den) he.symm)

private theorem twoPower_bounded (j : ℕ) : Bounded ((2 : ℚ) ^ j) (j + 1) := by
  refine ⟨2^j, 1, by decide, by norm_num, ?_, ?_⟩
  · exact Nat.pow_lt_pow_right (by decide) (by omega)
  · exact Nat.one_lt_pow (by omega) (by decide)

theorem scoreLevel_bounded {L : ℕ} {tag : PacketLevel} (h : tag ∈ boundedLevels L) :
    Bounded tag.weightRat (L + 4) := by
  cases tag with
  | unit => exact bounded_one.mono (by omega)
  | half j =>
    have hJ : j < L := by simpa [boundedLevels] using h
    unfold PacketLevel.weightRat
    exact (bounded_one.div (twoPower_bounded (j + 1)) (by positivity)).mono (by omega)
  | third j =>
    have hJ : j < L + 1 := by simpa [boundedLevels] using h
    unfold PacketLevel.weightRat
    have h3 : Bounded 3 2 := ⟨3, 1, by decide, by norm_num, by decide, by decide⟩
    exact ((bounded_one.div (twoPower_bounded j) (by positivity)).div h3 (by norm_num)).mono
      (by omega)

theorem roundedScoreRat_bounded (L : ℕ) (x : ℚ) :
    Bounded (roundedScoreRat L x) (L + 4) := by
  let S := insert 0 (((boundedLevels L).map PacketLevel.weightRat).toFinset.filter (· ≤ x))
  have h : roundedScoreRat L x ∈ S := Finset.max'_mem S (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · rw [h]
    exact bounded_zero.mono (by omega)
  · obtain ⟨tag, htag, he⟩ :=
      List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
    rw [← he]
    exact scoreLevel_bounded htag

theorem scaleBreakpointRat_bounded {m L : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (i : Fin m × Fin L × Bool) :
    Bounded (scaleBreakpointRat v i) (valuationDigits v + L + 2) := by
  unfold scaleBreakpointRat
  have hf : Bounded (if i.2.2 then 3 else 1 : ℚ) 2 := by
    cases i.2.2 <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact bounded_one.mono (by decide)
    · exact ⟨3, 1, by decide, by norm_num, by decide, by decide⟩
  exact (((valuation_bounded v hv i.1).mul (twoPower_bounded i.2.1.val)).mul hf).mono
    (by have := i.2.1.isLt; omega)

/-- Packet scan work. At an iteration each trial examines the current
packet list at most once. Elementary packet-set updates are budgeted separately
from rational arithmetic. The recurrence follows the actual merge decisions. -/
def packetScanWork {m : ℕ} : ℕ → List (Packet m) → ℕ
  | 0, _ => 0
  | fuel + 1, P =>
    let scan := (P.length + 1)^2
    match packetStep P with
    | none => scan
    | some Q => scan + packetScanWork fuel Q

theorem packetScanWork_le {m M : ℕ} {w : Fin m → ℝ}
    (fuel : ℕ) (P : List (Packet m)) (hn : P.Nodup)
    (hv : ValidPackets w P.toFinset) (hM : P.length ≤ M) :
    packetScanWork fuel P ≤ fuel * (M + 1)^2 := by
  induction fuel generalizing P with
  | zero => simp [packetScanWork]
  | succ f ih =>
    have hs : (P.length + 1)^2 ≤ (M + 1)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    unfold packetScanWork
    cases h : packetStep P with
    | none =>
      change (P.length + 1)^2 ≤ (f + 1) * (M + 1)^2
      rw [Nat.add_mul, one_mul]
      omega
    | some Q =>
      have hf := packetStep_nodup hn hv h
      have hg := (packetStep_sound hn h).valid hv
      have hlt := hg.2.2
      rw [List.toFinset_card_of_nodup hf, List.toFinset_card_of_nodup hn] at hlt
      have hcost := ih Q hf hg.1 (hlt.le.trans hM)
      change (P.length + 1)^2 + packetScanWork f Q ≤ (f + 1) * (M + 1)^2
      rw [Nat.add_mul, one_mul]
      omega

theorem preparedMenu_packetScanWork_le {m : ℕ} (tag : Fin m → Option PacketLevel)
    (w : Fin m → ℝ) (R : Finset (Fin m))
    (hw : ∀ g, w g = (tag g).elim 0 PacketLevel.weight) :
    let P := initialPackets tag R
    packetScanWork P.length P ≤ R.card * (R.card + 1)^2 := by
  obtain ⟨hnd, hv, _, _⟩ := initialPackets_spec tag R w hw
  have hlen := initialPackets_length tag R
  exact (packetScanWork_le _ _ hnd hv hlen).trans (Nat.mul_le_mul_right _ hlen)

/-- Feasibility and bag scores sum at most m exact rational scores. -/
theorem roundedScoreRat_sum_bounded {m : ℕ} (L : ℕ) (x : Fin m → ℚ) (B : Finset (Fin m)) :
    Bounded (∑ g ∈ B, roundedScoreRat L (x g)) ((L + 5) * m + 1) := by
  let xs := (B.sort (· ≤ ·)).map (fun g => roundedScoreRat L (x g))
  have hx (q : ℚ) (hq : q ∈ xs) : Bounded q (L + 4) := by
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hq
    exact roundedScoreRat_bounded L (x g)
  have hs := bounded_sum xs (L + 4) hx
  have he : xs.sum = ∑ g ∈ B, roundedScoreRat L (x g) := by
    simpa only [xs, Finset.sort_toFinset] using
      (List.sum_toFinset (fun g => roundedScoreRat L (x g)) (B.sort_nodup (· ≤ ·))).symm
  have hl : xs.length ≤ m := by
    simp only [xs, List.length_map, Finset.length_sort]
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  rw [← he]
  exact hs.mono (by
    rw [show L + 4 + 1 = L + 5 by omega]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) _)

end OnlineMMS.TwoType
