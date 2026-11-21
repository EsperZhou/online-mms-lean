import OnlineMMS.Model
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace OnlineMMS.TwoType

noncomputable def dyadic (j : ℕ) : ℝ := 1 / (2 : ℝ) ^ j
noncomputable def thirds (j : ℕ) : ℝ := dyadic j / 3

private theorem dyadic_pos (j : ℕ) : 0 < dyadic j := by unfold dyadic; positivity

private theorem dyadic_step (j : ℕ) : dyadic (j + 1) = dyadic j / 2 := by
  simp only [dyadic, pow_succ, div_div]

private theorem exists_dyadic_le (x : ℝ) (hx : 0 < x) : ∃ j, dyadic j ≤ x := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / x) (by norm_num : (1 : ℝ) < 2)
  exact ⟨j, by
    unfold dyadic
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ hx).mp hj
    linarith only [hh]⟩

private noncomputable def lowerIndex (x : ℝ) (hx : 0 < x) : ℕ :=
  Nat.find (exists_dyadic_le x hx)

/-- Downward rounding to the dyadic and third-dyadic levels of the paper. -/
noncomputable def score (x : ℝ) : ℝ :=
  if hx : 0 < x then
    if 1 ≤ x then 1 else if 1 / 2 ≤ x then 1 / 2 else
      let j := lowerIndex x hx - 2
      if thirds j ≤ x then thirds j else dyadic (j + 2)
  else 0

private theorem smallIndex_spec {x : ℝ} (hx : 0 < x) (hh : x < 1 / 2) :
    let j := lowerIndex x hx - 2
    dyadic (j + 2) ≤ x ∧ x < dyadic (j + 1) := by
  let i := lowerIndex x hx
  have hi : dyadic i ≤ x := Nat.find_spec (exists_dyadic_le x hx)
  have hind : 2 ≤ i := by
    by_contra! h
    interval_cases i <;> norm_num [dyadic] at hi ⊢ <;> linarith
  have he : i - 2 + 2 = i := by omega
  have hf : i - 2 + 1 < i := by omega
  change dyadic (i - 2 + 2) ≤ x ∧ x < dyadic (i - 2 + 1)
  exact ⟨by rwa [he], lt_of_not_ge (Nat.find_min (exists_dyadic_le x hx) hf)⟩

private theorem score_shape {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ score x ∧ score x ≤ x ∧
      ((x = 0 ∧ score x = 0) ∨ score x = 1 ∨ (score x = 1 / 2 ∧ x < 1) ∨
        (((∃ j, score x = dyadic j) ∨ ∃ j, score x = thirds j) ∧
          x < 3 / 2 * score x)) := by
  classical
  by_cases hpos : 0 < x
  · by_cases hu : 1 ≤ x
    · simp [score, hpos, hu]
    by_cases hh : 1 / 2 ≤ x
    · have hxone : x < 1 := lt_of_not_ge hu
      simp only [score, dif_pos hpos, if_neg hu, if_pos hh]
      exact ⟨by norm_num, hh, Or.inr (Or.inr (Or.inl ⟨trivial, hxone⟩))⟩
    · let j := lowerIndex x hpos - 2
      obtain ⟨hj, hp⟩ := smallIndex_spec hpos (lt_of_not_ge hh)
      change dyadic (j + 2) ≤ x at hj
      change x < dyadic (j + 1) at hp
      have hs : 0 < dyadic j := dyadic_pos _
      by_cases ht : thirds j ≤ x
      · have he : score x = thirds j := by
          unfold score
          rw [dif_pos hpos, if_neg hu, if_neg hh]
          exact if_pos ht
        rw [he]
        refine ⟨(div_pos hs (by norm_num)).le, ht, ?_⟩
        right; right; right
        refine ⟨Or.inr ⟨j, rfl⟩, ?_⟩
        rw [dyadic_step] at hp
        unfold thirds
        linarith
      · have he : score x = dyadic (j + 2) := by
          unfold score
          rw [dif_pos hpos, if_neg hu, if_neg hh]
          exact if_neg ht
        rw [he]
        refine ⟨(dyadic_pos _).le, hj, ?_⟩
        right; right; right
        refine ⟨Or.inl ⟨j + 2, rfl⟩, ?_⟩
        have hh' := lt_of_not_ge ht
        unfold thirds at hh'
        rw [dyadic_step, dyadic_step]
        linarith
  · have hz : x = 0 := le_antisymm (le_of_not_gt hpos) hx
    simp [score, hpos, hz]

theorem score_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ score x := (score_shape hx).1

theorem score_le_value {x : ℝ} (hx : 0 ≤ x) : score x ≤ x := (score_shape hx).2.1

theorem score_level {x : ℝ} (hx : 0 ≤ x) (hs : 0 < score x) :
    (∃ j, score x = dyadic j) ∨ ∃ j, score x = thirds j := by
  rcases (score_shape hx).2.2 with ⟨_, hz⟩ | hu | ⟨hh, _⟩ | ⟨h, _⟩
  · linarith
  · exact Or.inl ⟨0, by simpa [dyadic] using hu⟩
  · exact Or.inl ⟨1, by simpa [dyadic] using hh⟩
  · exact h

private theorem dyadic_antitone : Antitone dyadic := by
  intro i j hij
  unfold dyadic
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij)

private theorem thirds_antitone : Antitone thirds := by
  intro i j hij
  exact div_le_div_of_nonneg_right (dyadic_antitone hij) (by norm_num)

private theorem all_level_bounds (x : ℝ) :
    (∀ i, dyadic i ≤ x → dyadic i ≤ score x) ∧
    (∀ i, thirds i ≤ x → thirds i ≤ score x) := by
  classical
  by_cases hpos : 0 < x
  · by_cases hu : 1 ≤ x
    · rw [show score x = 1 by simp [score, hpos, hu]]
      constructor
      · intro i _
        have h := dyadic_antitone (Nat.zero_le i)
        simpa [dyadic] using h
      · intro i _
        have h := thirds_antitone (Nat.zero_le i)
        have hbase : thirds 0 ≤ 1 := by norm_num [thirds, dyadic]
        exact h.trans hbase
    · by_cases hh : 1 / 2 ≤ x
      · rw [show score x = 1 / 2 by simp only [score, dif_pos hpos, if_neg hu, if_pos hh]]
        constructor
        · intro i hi
          have hip : 1 ≤ i := by
            apply le_of_not_gt
            intro h0
            have he : i = 0 := by omega
            rw [he] at hi
            norm_num [dyadic] at hi
            exact hu hi
          have h := dyadic_antitone hip
          simpa [dyadic] using h
        · intro i _
          have h := thirds_antitone (Nat.zero_le i)
          exact h.trans (by norm_num [thirds, dyadic])
      · let j := lowerIndex x hpos - 2
        obtain ⟨_, hprev⟩ := smallIndex_spec hpos (lt_of_not_ge hh)
        change x < dyadic (j + 1) at hprev
        have hd (i : ℕ) (hi : dyadic i ≤ x) : dyadic i ≤ dyadic (j + 2) := by
          apply dyadic_antitone
          apply le_of_not_gt
          intro h
          exact (not_le_of_gt (hprev.trans_le (dyadic_antitone (by omega : i ≤ j + 1)))) hi
        have ht (i : ℕ) (hi : thirds i ≤ x) : j ≤ i := by
          apply le_of_not_gt
          intro h
          have hp := dyadic_antitone (by omega : i + 2 ≤ j + 1)
          have hprev' : dyadic (j + 1) = dyadic j / 2 := dyadic_step j
          have hip : dyadic (i + 2) = dyadic i / 2 / 2 := by rw [dyadic_step, dyadic_step]
          rw [hprev', hip] at hp
          rw [hprev'] at hprev
          have hposi := dyadic_pos i
          unfold thirds at hi
          linarith
        have he : score x = if thirds j ≤ x then thirds j else dyadic (j + 2) := by
          simp only [score, dif_pos hpos, if_neg hu, if_neg hh]
          rfl
        rw [he]
        split_ifs with hs
        · constructor
          · intro i hi
            apply (hd i hi).trans
            rw [dyadic_step, dyadic_step, thirds]
            linarith [dyadic_pos j]
          · exact fun i hi => thirds_antitone (ht i hi)
        · constructor
          · exact hd
          · intro i hi
            have hc : j + 1 ≤ i := by
              have h0 := ht i hi
              apply le_of_not_gt
              intro h
              have heq : i = j := by omega
              exact hs (heq ▸ hi)
            apply (thirds_antitone hc).trans
            rw [thirds, dyadic_step, dyadic_step, dyadic_step]
            linarith [dyadic_pos j]
  · constructor
    · intro i hi
      exact False.elim (hpos ((dyadic_pos i).trans_le hi))
    · intro i hi
      exact False.elim (hpos ((div_pos (dyadic_pos i) (by norm_num : (0 : ℝ) < 3)).trans_le hi))

/-- The rounded score dominates every admissible level. Combined with
`score_level` and `score_le_value`, this identifies the manuscript's maximum. -/
theorem score_ge_level {x z : ℝ}
    (hz : (∃ i, z = dyadic i) ∨ ∃ i, z = thirds i) (hle : z ≤ x) : z ≤ score x := by
  rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact (all_level_bounds x).1 i hle
  · exact (all_level_bounds x).2 i hle

theorem score_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : score x ≤ score y := by
  by_cases hp : 0 < score x
  · exact score_ge_level (score_level hx hp) ((score_le_value hx).trans hxy)
  · exact (le_of_not_gt hp).trans (score_nonneg (hx.trans hxy))

theorem score_half_range {x : ℝ} (hx : 1 / 2 ≤ x) (hhi : x < 1) :
    score x = 1 / 2 := by
  have hpos : 0 < x := by linarith
  simp only [score, dif_pos hpos, if_neg (not_le_of_gt hhi), if_pos hx]

theorem score_thirds_range {x : ℝ} (j : ℕ) (hlo : thirds j ≤ x)
    (hhi : x < 3 / 2 * thirds j) : score x = thirds j := by
  have hp : 0 < thirds j := by unfold thirds; exact div_pos (dyadic_pos _) (by norm_num)
  have hge := score_ge_level (Or.inr ⟨j, rfl⟩) hlo
  refine le_antisymm ?_ hge
  have hs := score_level (hp.le.trans hlo) (hp.trans_le hge)
  have hf := (score_le_value (hp.le.trans hlo)).trans_lt hhi
  rcases hs with ⟨i, he⟩ | ⟨i, he⟩
  · rw [he]
    have hprev : x < dyadic (j + 1) := by rw [dyadic_step]; unfold thirds at hhi; linarith
    have hie : j + 2 ≤ i := by
      apply le_of_not_gt
      intro hn
      have hbound := dyadic_antitone (show i ≤ j + 1 by omega)
      rw [he] at hf
      unfold thirds at hf
      rw [dyadic_step] at hbound
      linarith
    apply (dyadic_antitone hie).trans
    rw [dyadic_step, dyadic_step, thirds]
    linarith [dyadic_pos j]
  · rw [he]
    apply thirds_antitone
    apply le_of_not_gt
    intro hn
    have hh := thirds_antitone (show i + 1 ≤ j by omega)
    unfold thirds at hh hp
    rw [dyadic_step] at hh
    rw [he] at hf
    change dyadic i / 3 < 3 / 2 * (dyadic j / 3) at hf
    linarith

theorem score_pos {x : ℝ} (hx : 0 < x) : 0 < score x := by
  obtain ⟨j, hj⟩ := exists_dyadic_le x hx
  exact (dyadic_pos j).trans_le (score_ge_level (Or.inl ⟨j, rfl⟩) hj)

private theorem value_le_mul_score {x : ℝ} (hx : 0 ≤ x)
    (hu : score x ≠ 1) (hh : score x ≠ 1 / 2) : x ≤ 3 / 2 * score x := by
  rcases (score_shape hx).2.2 with ⟨h, hz⟩ | h | ⟨h, _⟩ | ⟨_, h⟩
  · rw [hz, h]
    norm_num
  · exact False.elim (hu h)
  · exact False.elim (hh h)
  · exact h.le

/-- A bundle worth 7/4 payment units has at least one unit of score. -/
theorem score_initialization {m : ℕ} (x : Fin m → ℝ) (hx : ∀ g, 0 ≤ x g)
    (S : Finset (Fin m)) (hvalue : (7 / 4 : ℝ) ≤ bundleValue x S) :
    1 ≤ bundleValue (fun g => score (x g)) S := by
  classical
  by_contra! hsum
  let w := fun g => score (x g)
  have hw (g : Fin m) : 0 ≤ w g := score_nonneg (hx g)
  have hlt (g : Fin m) (hg : g ∈ S) : w g < 1 :=
    (Finset.single_le_sum (fun i _ => hw i) hg).trans_lt hsum
  by_cases hhalf : ∃ g ∈ S, w g = 1 / 2
  · obtain ⟨g, hg, hgw⟩ := hhalf
    have htail : bundleValue w (S.erase g) < 1 / 2 := by
      have hsplit := Finset.sum_erase_add S w hg
      change bundleValue w (S.erase g) + w g = bundleValue w S at hsplit
      linarith
    have hgval : x g < 1 := by
      rcases (score_shape (hx g)).2.2 with ⟨h, _⟩ | h | ⟨_, h⟩ | ⟨_, h⟩
      · linarith
      · exact False.elim ((ne_of_lt (hlt g hg)) h)
      · exact h
      · change w g = 1 / 2 at hgw
        change x g < 3 / 2 * w g at h
        linarith
    have htailbound : bundleValue x (S.erase g) ≤ 3 / 2 * bundleValue w (S.erase g) := by
      unfold bundleValue
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hm := (Finset.mem_erase.mp hi).2
      apply value_le_mul_score (hx i) (ne_of_lt (hlt i hm))
      intro he
      have hilim := Finset.single_le_sum (fun j _ => hw j) hi
      change w i ≤ bundleValue w (S.erase g) at hilim
      change w i = 1 / 2 at he
      linarith
    have hsplit := Finset.sum_erase_add S x hg
    change bundleValue x (S.erase g) + x g = bundleValue x S at hsplit
    linarith
  · have hbound : bundleValue x S ≤ 3 / 2 * bundleValue w S := by
      unfold bundleValue
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => value_le_mul_score (hx i)
        (ne_of_lt (hlt i hi)) (fun he => hhalf ⟨i, hi, he⟩)
    linarith

end OnlineMMS.TwoType
