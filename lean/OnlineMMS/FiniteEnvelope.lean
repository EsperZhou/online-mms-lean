import OnlineMMS.FixedWidthProduct
import OnlineMMS.Baseline
import Mathlib.Data.Nat.Sqrt

namespace OnlineMMS.FixedWidth

private def ceilSquareDiv (a d : ℕ) : ℕ :=
  let s := Nat.sqrt (a / d)
  if a ≤ d * s^2 then s else s + 1

private theorem ceilSquareDiv_le_iff (a d b : ℕ) (hd : 0 < d) :
    ceilSquareDiv a d ≤ b ↔ a ≤ d * b^2 := by
  let s := Nat.sqrt (a / d)
  have hlo : d * s^2 ≤ a := by
    change d * s^2 ≤ a
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Nat.sqrt_le' (a / d))
  have hhi : a < d * (s + 1)^2 := by
    have h := (Nat.sqrt_lt').mp (Nat.lt_succ_self (Nat.sqrt (a / d)))
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp h
  have hsquare {q j : ℕ} (h : q ≤ j) : d * q^2 ≤ d * j^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
  have hstrict {q j : ℕ} (h : q < j) : d * q^2 < d * j^2 :=
    Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left h (by decide)) hd
  change (if a ≤ d * s^2 then s else s + 1) ≤ b ↔ a ≤ d * b^2
  by_cases h : a ≤ d * s^2
  · rw [if_pos h]
    refine ⟨fun hb => h.trans (hsquare hb), fun hb => ?_⟩
    by_contra! hf
    exact (Nat.not_lt_of_ge (hlo.trans hb)) (hstrict hf)
  · rw [if_neg h]
    refine ⟨fun hb => hhi.le.trans (hsquare hb), fun hb => ?_⟩
    by_contra! hf
    exact h (hb.trans (hsquare (by omega)))

private theorem ceil_sqrt_le {x : ℝ} {d a : ℕ} (hd : 0 < d)
    (hx : 0 ≤ x) (he : x^2 * (d : ℝ) = (a : ℝ)) (b : ℕ) :
    Nat.ceil x ≤ b ↔ ceilSquareDiv a d ≤ b := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Nat.ceil_le, ceilSquareDiv_le_iff _ _ _ hd]
  constructor
  · intro h
    have hpow := pow_le_pow_left₀ hx h 2
    have hh := mul_le_mul_of_nonneg_right hpow hdR.le
    rw [he, mul_comm] at hh
    exact_mod_cast hh
  · intro h
    have hr : (a : ℝ) ≤ (d : ℝ) * (b : ℝ)^2 := by exact_mod_cast h
    rw [← he, mul_comm (d : ℝ)] at hr
    have hs := (mul_le_mul_right hdR).mp hr
    by_contra! hb
    have := pow_lt_pow_left₀ hb (Nat.cast_nonneg b) (show (2 : ℕ) ≠ 0 by decide)
    linarith

private theorem ceil_sqrt_eq {x : ℝ} {d a : ℕ} (hd : 0 < d)
    (hx : 0 ≤ x) (he : x^2 * (d : ℝ) = (a : ℝ)) :
    Nat.ceil x = ceilSquareDiv a d :=
  le_antisymm ((ceil_sqrt_le hd hx he _).mpr le_rfl) ((ceil_sqrt_le hd hx he _).mp le_rfl)

private def gNat (k : ℕ) : ℕ := max 4 (ceilSquareDiv (4 * k) 1)
private def hNat (k : ℕ) : ℕ := 212 + 4 * ceilSquareDiv k 32

private theorem gNat_eq (k : ℕ) : productMultiplier k = gNat k := by
  unfold productMultiplier gNat
  congr 1
  refine ceil_sqrt_eq (by decide : 0 < 1) (by positivity) ?_
  push_cast
  have he := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith only [he]

private theorem hNat_eq (k : ℕ) : bucketMultiplier k = hNat k := by
  rw [bucketMultiplier_eq_ceil]
  unfold hNat
  congr 2
  refine ceil_sqrt_eq (by decide : 0 < 32) (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt (by positivity)]
  norm_num

private def compareDenominators (k product bucket : ℕ) : Prop :=
  (k ≤ 150 → k ≤ product ∧ k ≤ bucket) ∧
  (151 ≤ k → k ≤ 1640 → product ≤ k ∧ product ≤ bucket) ∧
  (1641 ≤ k → bucket ≤ k ∧ bucket ≤ product) ∧
  (k = product ∧ k ≤ bucket ↔ k = 144 ∨ k = 150) ∧
  (product = bucket ∧ product ≤ k ↔ 1561 ≤ k ∧ k ≤ 1568) ∧
  ¬ (k = bucket ∧ k ≤ product)

private instance (k product bucket : ℕ) : Decidable (compareDenominators k product bucket) := by
  unfold compareDenominators
  infer_instance

private abbrev finiteComparison (k : ℕ) :=
  compareDenominators k (6 * gNat k) (2 * hNat k)

/-- Search the integer interval [lo, lo + 2^bits) for the least b with a ≤ d * b². -/
private def ceilSquareSearch (a d : ℕ) : ℕ → ℕ → ℕ
  | 0, lo => lo
  | bits + 1, lo =>
    let mid := lo + 2^bits
    if a ≤ d * (mid - 1)^2 then ceilSquareSearch a d bits lo
    else ceilSquareSearch a d bits mid

private theorem ceilSquareSearch_eq (a d bits lo : ℕ) (hd : 0 < d)
    (hl : lo ≤ ceilSquareDiv a d) (hu : ceilSquareDiv a d < lo + 2^bits) :
    ceilSquareSearch a d bits lo = ceilSquareDiv a d := by
  induction bits generalizing lo with
  | zero =>
    simp [ceilSquareSearch] at *
    omega
  | succ bits ih =>
    rw [ceilSquareSearch]
    have : 0 < 2 ^ bits := by positivity
    rw [Nat.pow_succ] at hu
    split
    next h =>
      apply ih _ hl
      have := (ceilSquareDiv_le_iff _ _ _ hd).mpr h
      omega
    next h =>
      apply ih
      · have := mt (ceilSquareDiv_le_iff _ _ _ hd).mp h
        omega
      · omega

/-- On this range the ceilings are at most 82 and 8, fitting in seven and four bits. -/
private def checkComparison (k : ℕ) : Bool :=
  let product := 6 * max 4 (ceilSquareSearch (4 * k) 1 7 0)
  let bucket := 2 * (212 + 4 * ceilSquareSearch k 32 4 0)
  decide (compareDenominators k product bucket)

private theorem all_comparisons : (List.range 1681).all checkComparison = true := by
  decide +kernel

private theorem finite_comparison_small : ∀ k : Fin 1681, finiteComparison k.val := by
  intro k
  have h := List.all_eq_true.mp all_comparisons k.val (List.mem_range.mpr k.isLt)
  have hk := k.isLt
  have hg : ceilSquareDiv (4 * k.val) 1 ≤ 82 := by
    apply (ceilSquareDiv_le_iff _ _ _ (by decide)).mpr
    omega
  have hh : ceilSquareDiv k.val 32 ≤ 8 := by
    apply (ceilSquareDiv_le_iff _ _ _ (by decide)).mpr
    omega
  simpa only [checkComparison, decide_eq_true_eq,
    ceilSquareSearch_eq (4 * k.val) 1 7 0 (by decide) (Nat.zero_le _) (by omega),
    ceilSquareSearch_eq k.val 32 4 0 (by decide) (Nat.zero_le _) (by omega),
    finiteComparison, gNat, hNat] using h

private theorem finite_comparison_certificate {k : ℕ} (hk : k < 1681) :
    finiteComparison k := by
  exact finite_comparison_small ⟨k, hk⟩

private theorem large_comparison {k : ℕ} (hk : 1681 ≤ k) :
    2 * bucketMultiplier k < k ∧ 2 * bucketMultiplier k < 6 * productMultiplier k := by
  let s := Real.sqrt (k : ℝ)
  have hs : 41 ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hk
  have hscale : Real.sqrt ((k : ℝ) / 2) ≤ (5 / 7 : ℝ) * s := by
    apply Real.sqrt_le_iff.mpr
    have hn : 0 ≤ s := Real.sqrt_nonneg _
    have hsq : s^2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    exact ⟨by positivity, by nlinarith only [hsq, Nat.cast_nonneg (α := ℝ) k]⟩
  have hh := (bucketMultiplier_estimate (by omega : 0 < k)).2
  have h2h : 2 * (bucketMultiplier k : ℝ) < 12 * s := by linarith
  have hsquare : s^2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsK : 12 * s ≤ k := by
    have hmul := mul_nonneg (sub_nonneg.mpr (show 12 ≤ s by linarith))
      (show 0 ≤ s by linarith)
    nlinarith only [hsquare, hmul]
  have hg : 2 * s ≤ (productMultiplier k : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 4 (Nat.ceil (2 * Real.sqrt (k : ℝ)))))
  have hg6 : 12 * s ≤ 6 * (productMultiplier k : ℝ) := by linarith
  exact ⟨by exact_mod_cast h2h.trans_le hsK, by exact_mod_cast h2h.trans_le hg6⟩

/-- The manuscript's finite-k comparison of its three explicit guarantees. -/
theorem finite_envelope_denominators (k : ℕ) :
    (k ≤ 150 → k ≤ 6 * productMultiplier k ∧ k ≤ 2 * bucketMultiplier k) ∧
    (151 ≤ k → k ≤ 1640 → 6 * productMultiplier k ≤ k ∧
      6 * productMultiplier k ≤ 2 * bucketMultiplier k) ∧
    (1641 ≤ k → 2 * bucketMultiplier k ≤ k ∧
      2 * bucketMultiplier k ≤ 6 * productMultiplier k) := by
  by_cases hk : k < 1681
  · have h := finite_comparison_certificate hk
    exact ⟨by simpa [gNat_eq, hNat_eq] using h.1,
      by simpa [gNat_eq, hNat_eq] using h.2.1,
      by simpa [gNat_eq, hNat_eq] using h.2.2.1⟩
  · have h := large_comparison (k := k) (by omega)
    exact ⟨fun h => False.elim (by omega), fun _ h => False.elim (by omega),
      fun _ => ⟨h.1.le, h.2.le⟩⟩

/-- The comparisons also identify precisely which guarantees tie for first. -/
theorem finite_envelope_ties (k : ℕ) :
    (k = 6 * productMultiplier k ∧ k ≤ 2 * bucketMultiplier k ↔ k = 144 ∨ k = 150) ∧
    (6 * productMultiplier k = 2 * bucketMultiplier k ∧ 6 * productMultiplier k ≤ k ↔
      1561 ≤ k ∧ k ≤ 1568) ∧
    ¬ (k = 2 * bucketMultiplier k ∧ k ≤ 6 * productMultiplier k) := by
  by_cases hk : k < 1681
  · have h := finite_comparison_certificate hk
    simpa [gNat_eq, hNat_eq] using h.2.2.2
  · obtain ⟨h₁, h₂⟩ := large_comparison (k := k) (by omega)
    exact ⟨⟨fun h => by omega, fun h => by omega⟩,
      ⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩

/-- The manuscript's explicit lower bound L(k). -/
noncomputable def finiteEnvelope (k : ℕ) : ℝ :=
  max (1 / (k : ℝ)) (max (1 / (6 * (productMultiplier k : ℝ)))
    (1 / (2 * (bucketMultiplier k : ℝ))))

/-- The best of the three stated explicit lower bounds is a uniform MMS bound. -/
theorem finite_envelope_le_alphaMMS {k : ℕ} (hk : 0 < k) : finiteEnvelope k ≤ alphaMMS k := by
  apply max_le (one_over_k_le_alphaMMS hk)
  apply max_le _ ((explicit_fraction_le_alphaTPS hk).trans (alphaTPS_le_alphaMMS k))
  have hg : (4 : ℝ) ≤ productMultiplier k := by exact_mod_cast (productMultiplier_bounds k).1
  apply le_uniformFactor
  · exact ⟨by positivity, (div_le_one₀ (by positivity)).mpr (by linarith)⟩
  · intro n hn m v hv
    obtain ⟨policy, hp⟩ := fixed_width_product_guarantee hn hk v hv
    refine ⟨policy, hp.mono (fun t => ?_)⟩
    have he := div_le_div_of_nonneg_right (maximinShare_le_truncatedShare (v t) (hv t) hn)
      (show (0 : ℝ) ≤ 6 * productMultiplier k by positivity)
    simpa [div_eq_mul_inv, mul_comm] using he

theorem finite_envelope_from_1641 {k : ℕ} (hk : 1641 ≤ k) :
    finiteEnvelope k = 1 / (2 * (bucketMultiplier k : ℝ)) := by
  obtain ⟨h₁, h₂⟩ := (finite_envelope_denominators k).2.2 hk
  have hh : (216 : ℝ) ≤ bucketMultiplier k :=
    by exact_mod_cast (bucketMultiplier_bounds (by omega : 0 < k)).1
  have hp : (0 : ℝ) < 2 * bucketMultiplier k := by linarith
  unfold finiteEnvelope
  rw [max_eq_right (one_div_le_one_div_of_le hp (by exact_mod_cast h₂)),
    max_eq_right (one_div_le_one_div_of_le hp (by exact_mod_cast h₁))]

/-- Exact values underlying the two reported decimal approximations. -/
theorem finite_envelope_examples :
    Real.sqrt (10000 : ℝ) * finiteEnvelope 10000 = 100 / 568 ∧
    Real.sqrt (1000000 : ℝ) * finiteEnvelope 1000000 = 1000 / 1840 := by
  have h₁ : bucketMultiplier 10000 = 284 := by rw [hNat_eq]; decide
  have h₂ : bucketMultiplier 1000000 = 920 := by
    have hle : ceilSquareDiv 1000000 32 ≤ 177 :=
      (ceilSquareDiv_le_iff _ _ _ (by decide)).mpr (by norm_num)
    have hnot : ¬ ceilSquareDiv 1000000 32 ≤ 176 := by
      rw [ceilSquareDiv_le_iff _ _ _ (by decide)]
      norm_num
    have he : ceilSquareDiv 1000000 32 = 177 := by omega
    rw [hNat_eq, hNat, he]
  rw [finite_envelope_from_1641 (by decide : 1641 ≤ 10000),
    finite_envelope_from_1641 (by decide : 1641 ≤ 1000000), h₁, h₂]
  norm_num [show (10000 : ℝ) = 100 ^ 2 by norm_num,
    show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq]

theorem sqrt_denominator_lt_alphaMMS {k : ℕ} (hk : 0 < k) :
    1 / (Real.sqrt (2 * (k : ℝ)) + 432) < alphaMMS k := by
  have hn : 0 ≤ (k : ℝ) / 32 := by positivity
  have he : 8 * Real.sqrt ((k : ℝ) / 32) = Real.sqrt (2 * (k : ℝ)) := by
    have ha := Real.sq_sqrt hn
    have hb := Real.sq_sqrt (show 0 ≤ 2 * (k : ℝ) by positivity)
    have ha0 := Real.sqrt_nonneg ((k : ℝ) / 32)
    have hb0 := Real.sqrt_nonneg (2 * (k : ℝ))
    have hsq : (8 * Real.sqrt ((k : ℝ) / 32))^2 = Real.sqrt (2 * (k : ℝ))^2 := by
      nlinarith only [ha, hb]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).elim id (fun h => by linarith)
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((k : ℝ) / 32))
  have hupper : 2 * (bucketMultiplier k : ℝ) < Real.sqrt (2 * (k : ℝ)) + 432 := by
    rw [bucketMultiplier_eq_ceil]
    push_cast
    linarith
  have hh : (216 : ℝ) ≤ bucketMultiplier k := by exact_mod_cast (bucketMultiplier_bounds hk).1
  exact (one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < 2 * bucketMultiplier k) hupper).trans_le
    ((explicit_fraction_le_alphaTPS hk).trans (alphaTPS_le_alphaMMS k))

end OnlineMMS.FixedWidth
