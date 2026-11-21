import OnlineMMS.TwoTypeBreakpoints
import OnlineMMS.TwoTypePacketMerge
import Mathlib.Data.Rat.Cast.Order

namespace OnlineMMS.TwoType

def PacketLevel.weightRat : PacketLevel → ℚ
  | .unit => 1
  | .half j => 1 / 2 ^ (j + 1)
  | .third j => (1 / 2 ^ j) / 3

@[simp] theorem PacketLevel.weightRat_cast (tag : PacketLevel) :
    (tag.weightRat : ℝ) = tag.weight := by
  cases tag <;> simp [weightRat, weight, thirds, dyadic]

private theorem PacketLevel.weightRat_pos (tag : PacketLevel) : 0 < tag.weightRat := by
  cases tag <;> unfold weightRat <;> positivity

/-- Enumerate the bounded score levels in a fixed order. -/
def boundedLevels (L : ℕ) : List PacketLevel :=
  .unit :: ((List.range L).map PacketLevel.half ++ (List.range (L + 1)).map PacketLevel.third)

theorem boundedLevels_length (L : ℕ) : (boundedLevels L).length = 2 * L + 2 := by
  simp [boundedLevels]
  omega

private theorem half_mem_boundedLevels {j L : ℕ} (hj : j < L) :
    PacketLevel.half j ∈ boundedLevels L := by simp [boundedLevels, hj]

private theorem third_mem_boundedLevels {j L : ℕ} (hj : j ≤ L) :
    PacketLevel.third j ∈ boundedLevels L := by
  simp [boundedLevels, Nat.lt_succ_of_le hj]

private theorem weight_mem_real_levels (tag : PacketLevel) :
    (∃ j, tag.weight = dyadic j) ∨ ∃ j, tag.weight = thirds j := by
  cases tag with
  | unit => exact Or.inl ⟨0, by simp [PacketLevel.weight, dyadic]⟩
  | half j => exact Or.inl ⟨j + 1, rfl⟩
  | third j => exact Or.inr ⟨j, rfl⟩

/-- The candidate scores can be computed by finite rational arithmetic. -/
def roundedScoreRat (L : ℕ) (x : ℚ) : ℚ :=
  (insert 0 (((boundedLevels L).map PacketLevel.weightRat).toFinset.filter (· ≤ x))).max'
    (Finset.insert_nonempty _ _)

theorem roundedScoreRat_correct (L : ℕ) (x : ℚ) (hx : 0 ≤ x)
    (hL : 0 < x → dyadic L ≤ (x : ℝ)) :
    (roundedScoreRat L x : ℝ) = score (x : ℝ) := by
  classical
  let S := insert 0 (((boundedLevels L).map PacketLevel.weightRat).toFinset.filter (· ≤ x))
  have hs := Finset.max'_mem S (Finset.insert_nonempty _ _)
  change roundedScoreRat L x ∈ S at hs
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlower (tag : PacketLevel) (hm : tag ∈ boundedLevels L) (hte : tag.weight ≤ (x : ℝ)) :
      tag.weight ≤ (roundedScoreRat L x : ℝ) := by
    rw [← PacketLevel.weightRat_cast]
    have htQ : tag.weightRat ≤ x := by
      have hh : (tag.weightRat : ℝ) ≤ x := PacketLevel.weightRat_cast tag ▸ hte
      exact_mod_cast hh
    have hmem : tag.weightRat ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨tag, hm, rfl⟩), htQ⟩)
    have hh : tag.weightRat ≤ roundedScoreRat L x := Finset.le_max' S _ hmem
    exact_mod_cast hh
  have hz : (0 : ℝ) ≤ (roundedScoreRat L x : ℝ) := by
    have h : 0 ≤ roundedScoreRat L x := Finset.le_max' S 0 (Finset.mem_insert_self _ _)
    exact_mod_cast h
  refine le_antisymm ?_ ?_
  · rcases Finset.mem_insert.mp hs with he | he
    · simpa [he] using score_nonneg hxR
    · obtain ⟨hm, hq⟩ := Finset.mem_filter.mp he
      obtain ⟨tag, _, htag⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      have hqr : ((roundedScoreRat L x : ℚ) : ℝ) ≤ x := by exact_mod_cast hq
      rw [← htag, PacketLevel.weightRat_cast] at hqr ⊢
      exact score_ge_level (weight_mem_real_levels tag) hqr
  · by_cases hp : 0 < score (x : ℝ)
    · have hxpos : 0 < x := by
        have hh := hp.trans_le (score_le_value hxR)
        exact_mod_cast hh
      let k : PacketLevel := if L = 0 then .unit else .half (L - 1)
      have hk : k.weight = dyadic L := by
        by_cases h : L = 0
        · subst L
          norm_num [k, PacketLevel.weight, dyadic]
        · have he : L - 1 + 1 = L := by omega
          simp [k, h, PacketLevel.weight, he]
      have hkMem : k ∈ boundedLevels L := by
        by_cases h : L = 0
        · simp [k, h, boundedLevels]
        · simpa [k, h] using half_mem_boundedLevels (show L - 1 < L by omega)
      have hkLe : dyadic L ≤ (roundedScoreRat L x : ℝ) := by
        rw [← hk]
        exact hlower k hkMem (hk ▸ hL hxpos)
      have hmono {j : ℕ} (hj : L ≤ j) : dyadic j ≤ dyadic L := by
        unfold dyadic
        exact div_le_div_of_nonneg_left zero_le_one (by positivity)
          (pow_le_pow_right₀ (by norm_num) hj)
      have hle := score_le_value hxR
      rcases score_level hxR hp with ⟨j, hj⟩ | ⟨j, hj⟩
      · rcases j with _ | j
        · rw [hj]
          simpa [dyadic, PacketLevel.weight] using
            hlower .unit (by simp [boundedLevels]) (by simpa [hj, PacketLevel.weight, dyadic] using hle)
        · by_cases hjL : j < L
          · rw [hj]
            exact hlower (.half j) (half_mem_boundedLevels hjL) (by simpa [hj, PacketLevel.weight] using hle)
          · rw [hj]
            exact (hmono (by omega)).trans hkLe
      · by_cases hjL : j ≤ L
        · rw [hj]
          exact hlower (.third j) (third_mem_boundedLevels hjL) (by simpa [hj, PacketLevel.weight] using hle)
        · rw [hj]
          have ht : thirds j ≤ dyadic j := by
            unfold thirds
            exact div_le_self (by unfold dyadic; positivity) (by norm_num)
          exact ht.trans ((hmono (by omega)).trans hkLe)
    · exact (le_of_not_gt hp).trans hz

/-- Find a discrete tag for the score of an item, or discard it at score zero. -/
def roundedTagRat (L : ℕ) (x : ℚ) : Option PacketLevel :=
  (boundedLevels L).find? (fun tag => decide (tag.weightRat = roundedScoreRat L x))

theorem roundedTagRat_weight (L : ℕ) (x : ℚ) (hx : 0 ≤ x)
    (hL : 0 < x → dyadic L ≤ (x : ℝ)) :
    ((roundedTagRat L x).elim 0 PacketLevel.weight) = score (x : ℝ) := by
  classical
  let q := roundedScoreRat L x
  have hq := roundedScoreRat_correct L x hx hL
  cases he : roundedTagRat L x with
  | some tag =>
    have hEq : tag.weightRat = q := by
      have h := List.find?_some (p := fun t : PacketLevel => decide (t.weightRat = q)) he
      exact of_decide_eq_true h
    simp only [Option.elim_some, ← PacketLevel.weightRat_cast, hEq, q, hq]
  | none =>
    have hm := Finset.max'_mem
      (insert 0 (((boundedLevels L).map PacketLevel.weightRat).toFinset.filter (· ≤ x)))
      (Finset.insert_nonempty _ _)
    change q ∈ insert 0 (((boundedLevels L).map PacketLevel.weightRat).toFinset.filter (· ≤ x)) at hm
    rcases Finset.mem_insert.mp hm with hh | hh
    · change roundedScoreRat L x = 0 at hh
      simpa [hh] using hq
    · obtain ⟨tag, ht, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hh).1)
      have hn := List.find?_eq_none.mp he tag ht
      simp [q, heq] at hn

end OnlineMMS.TwoType
