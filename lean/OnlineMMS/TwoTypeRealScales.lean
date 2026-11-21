import OnlineMMS.TwoTypeRationalPolicy

/-! The largest admissible scale and the packet labels for arbitrary nonnegative
real item values. Every positive level has a unique label. -/

namespace OnlineMMS.TwoType

open private admissibleScale_enough_goods from OnlineMMS.TwoTypeScalePreparation
open private fourSevenths_admissible from OnlineMMS.TwoTypeRationalPolicy

private theorem greatest_of_admissible {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (h : ∃ y, AdmissibleScale v n y) :
    ∃ y, IsGreatest {z | AdmissibleScale v n z} y := by
  classical
  obtain ⟨y,hy⟩ := h
  let S := Finset.univ.filter (fun g => 0 < v g)
  have hc : n ≤ S.card := admissibleScale_enough_goods hy
  obtain ⟨g,hg,hmin⟩ := S.exists_min_image v (Finset.card_pos.mp (hn.trans_le hc))
  have ha : 0 < v g := (Finset.mem_filter.mp hg).2
  have hlower (i : Fin m) (hi : 0 < v i) : v g ≤ v i :=
    hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  let U := bundleValue v Finset.univ / n
  obtain ⟨L,hL⟩ := pow_unbounded_of_one_lt (U / v g) (by norm_num : (1:ℝ) < 2)
  have hL' : U < v g * 2 ^ L := by simpa [mul_comm] using (div_lt_iff₀ ha).mp hL
  obtain ⟨a,_,hmax⟩ := maximal_scale_by_breakpoints hn hv
    (admissibleScale_of_smallest ha hlower hc) hlower hL'
  exact ⟨a,hmax⟩

/-- The largest admissible positive scale, or zero if no such scale exists. -/
noncomputable def realScale {m : ℕ} (v : Fin m → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ y, IsGreatest {z | AdmissibleScale v n z} y then h.choose else 0

theorem realScale_spec {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    (realScale v n = 0 ∧ ∀ y, ¬ AdmissibleScale v n y) ∨
      IsGreatest {z | AdmissibleScale v n z} (realScale v n) := by
  classical
  unfold realScale
  split
  · rename_i h
    exact Or.inr h.choose_spec
  · rename_i h
    exact Or.inl ⟨rfl, fun y hy => h (greatest_of_admissible v hv hn ⟨y,hy⟩)⟩

theorem realScale_ge_four_sevenths {m n : ℕ} (v : Fin m → ℝ)
    (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    4/7 * maximinShare v n hn ≤ realScale v n := by
  rcases realScale_spec v hv hn with ⟨hz,hno⟩ | hmax
  · rw [hz]
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    exact le_of_not_gt (fun h => hno _ (fourSevenths_admissible v hv hn h))
  · by_cases hp : 0 < maximinShare v n hn
    · exact hmax.2 (fourSevenths_admissible v hv hn hp)
    · exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hp)).trans hmax.1.1.le

theorem realScale_eq_rationalScale {m n : ℕ} (v : Fin m → ℚ)
    (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    realScale (fun g => (v g : ℝ)) n = rationalScale v n := by
  rcases realScale_spec (fun g => (v g : ℝ)) (fun g => by change 0 ≤ (v g : ℝ); exact_mod_cast hv g) hn with h | h
  · rcases rationalScale_spec v hv hn with q | q
    · simp [h.1,q.1]
    · exact (h.2 _ q.1).elim
  · rcases rationalScale_spec v hv hn with q | q
    · exact (q.2 _ h.1).elim
    · exact h.unique q

private def denominator : PacketLevel → ℕ
  | .unit => 1
  | .half j => 2 ^ (j+1)
  | .third j => 3 * 2 ^ j

private theorem weight_eq_inverse (a : PacketLevel) : a.weight = 1 / (denominator a : ℝ) := by
  cases a <;> simp [PacketLevel.weight, denominator, dyadic, thirds, div_eq_mul_inv, mul_comm]

private theorem two_pow_ne_three_mul (i j : ℕ) : (2:ℕ)^i ≠ 3*2^j := by
  intro h
  have hd : (3:ℕ) ∣ 2^i := ⟨2^j,h⟩
  exact (by decide : ¬ (3:ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem denominator_injective : Function.Injective denominator := by
  have hpow : StrictMono (fun i : ℕ => (2:ℕ)^i) := pow_right_strictMono₀ (by decide)
  have hhalf (i : ℕ) : 1 < (2:ℕ)^(i+1) := one_lt_pow₀ (by decide) (by omega)
  have hthird (i : ℕ) : 1 < 3*(2:ℕ)^i := by have := pow_pos (by decide : 0 < (2:ℕ)) i; omega
  intro a b he
  cases a <;> cases b <;> simp only [denominator] at he
  · rfl
  · exact ((hhalf _).ne he).elim
  · exact ((hthird _).ne he).elim
  · exact ((hhalf _).ne' he).elim
  · congr 1; exact Nat.succ.inj (hpow.injective he)
  · exact (two_pow_ne_three_mul _ _ he).elim
  · exact ((hthird _).ne' he).elim
  · exact (two_pow_ne_three_mul _ _ he.symm).elim
  · congr 1; exact hpow.injective (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) he)

private theorem weight_injective : Function.Injective PacketLevel.weight := by
  intro a b h
  simp only [weight_eq_inverse, one_div, inv_inj] at h
  apply denominator_injective
  exact_mod_cast h

private theorem tag_injective : Function.Injective (fun q : Option PacketLevel => q.elim 0 PacketLevel.weight) := by
  have hp (a : PacketLevel) : 0 < a.weight := by
    cases a <;> simp only [PacketLevel.weight, thirds, dyadic] <;> positivity
  intro a b h
  cases a <;> cases b
  · rfl
  · exact ((hp _).ne h).elim
  · exact ((hp _).ne' h).elim
  · exact congrArg some (weight_injective h)

private theorem level_rep (x : ℝ) (hx : 0 ≤ x) :
    ∃ tag : Option PacketLevel, tag.elim 0 PacketLevel.weight = score x := by
  by_cases hp : 0 < score x
  · rcases score_level hx hp with ⟨j,hj⟩ | ⟨j,hj⟩
    · cases j with
      | zero => exact ⟨some .unit, by simpa [dyadic] using hj.symm⟩
      | succ j => exact ⟨some (.half j),hj.symm⟩
    · exact ⟨some (.third j),hj.symm⟩
  · exact ⟨none, le_antisymm (score_nonneg hx) (le_of_not_gt hp)⟩

noncomputable def realTag (x : ℝ) : Option PacketLevel :=
  if h : 0 ≤ x then (level_rep x h).choose else none

theorem realTag_weight {x : ℝ} (hx : 0 ≤ x) :
    (realTag x).elim 0 PacketLevel.weight = score x := by
  simpa [realTag,hx] using (level_rep x hx).choose_spec

theorem realTag_eq_roundedTagRat {m n : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (g : Fin m) :
    realTag ((v g : ℝ) / realScale (fun i => (v i : ℝ)) n) =
      roundedTagRat (scaleScanLimit v) (v g / rationalScale v n) := by
  rw [realScale_eq_rationalScale v hv hn]
  have hy : 0 ≤ (rationalScale v n : ℝ) := by
    rcases rationalScale_spec v hv hn with hz | h
    · simp [hz.1]
    · exact h.1.1.le
  apply tag_injective
  exact (realTag_weight (div_nonneg (show 0 ≤ (v g : ℝ) by exact_mod_cast hv g) hy)).trans
    (rationalScale_tag_correct v hv hn g).symm

end OnlineMMS.TwoType
