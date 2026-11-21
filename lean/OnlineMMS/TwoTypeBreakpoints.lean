import OnlineMMS.TwoTypeGuarantee

namespace OnlineMMS.TwoType

/-- Admissibility is measured on the goods of the original instance. -/
def AdmissibleScale {m : ℕ} (v : Fin m → ℝ) (n : ℕ) (y : ℝ) : Prop :=
  0 < y ∧ (n : ℝ) ≤ bundleValue (fun g => score (v g / y)) Finset.univ

noncomputable def scaleBreakpoint {m L : ℕ} (v : Fin m → ℝ)
    (i : Fin m × Fin L × Bool) : ℝ :=
  v i.1 * 2 ^ i.2.1.val * (if i.2.2 then 3 else 1)

open Classical in
/-- The search evaluates both endpoints and at most two breakpoints per
positive good and exponent. The range check discards irrelevant entries. -/
noncomputable def scaleCandidates {m : ℕ} (v : Fin m → ℝ) (a U : ℝ) (L : ℕ) :
    Finset ℝ :=
  insert a (insert U ((Finset.univ.image (scaleBreakpoint (L := L) v)).filter
    (fun z => a ≤ z ∧ z ≤ U)))

theorem scaleCandidates_card {m : ℕ} (v : Fin m → ℝ) (a U : ℝ) (L : ℕ) :
    (scaleCandidates v a U L).card ≤ 2 * m * L + 2 := by
  classical
  unfold scaleCandidates
  have hcard : ((Finset.univ : Finset (Fin m × Fin L × Bool)).image (scaleBreakpoint v)).card
      ≤ m * (L * 2) := by
    simpa using Finset.card_image_le
      (s := (Finset.univ : Finset (Fin m × Fin L × Bool))) (f := scaleBreakpoint v)
  have hfilter := (Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin m × Fin L × Bool)).image (scaleBreakpoint v))
    (p := fun z => a ≤ z ∧ z ≤ U)).trans hcard
  have h₁ := Finset.card_insert_le U ((Finset.univ.image (scaleBreakpoint (L := L) v)).filter
    (fun z => a ≤ z ∧ z ≤ U))
  have h₂ := Finset.card_insert_le a (insert U
    ((Finset.univ.image (scaleBreakpoint (L := L) v)).filter (fun z => a ≤ z ∧ z ≤ U)))
  have he : m * (L * 2) = 2 * m * L := by ring
  omega

/-- A feasible scale can never exceed the average original value. -/
theorem admissibleScale_le_average {m n : ℕ} (hn : 0 < n)
    {v : Fin m → ℝ} (hv : ∀ g, 0 ≤ v g) {y : ℝ} (hy : AdmissibleScale v n y) :
    y ≤ bundleValue v Finset.univ / n := by
  have hsum : (n : ℝ) ≤ bundleValue v Finset.univ / y := by
    apply hy.2.trans
    unfold bundleValue
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun g _ => score_le_value (div_nonneg (hv g) hy.1.le)
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  simpa [mul_comm] using (le_div_iff₀ hy.1).mp hsum

/-- The minimum positive item value is feasible whenever there are at least
as many positive items as arrivals. -/
theorem admissibleScale_of_smallest {m n : ℕ} {v : Fin m → ℝ} {a : ℝ}
    (ha : 0 < a) (hmin : ∀ g, 0 < v g → a ≤ v g)
    (hn : n ≤ (Finset.univ.filter (fun g => 0 < v g)).card) : AdmissibleScale v n a := by
  classical
  refine ⟨ha, ?_⟩
  have hscore (g : Fin m) (hg : 0 < v g) : score (v g / a) = 1 := by
    have h : 1 ≤ v g / a := (le_div_iff₀ ha).mpr (by simpa using hmin g hg)
    simp [score, (zero_lt_one.trans_le h), h]
  have hzero (g : Fin m) (hg : ¬ 0 < v g) : score (v g / a) = 0 := by
    have h : ¬ 0 < v g / a := not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hg) ha.le)
    simp [score, h]
  unfold bundleValue
  calc
    (n : ℝ) ≤ ((Finset.univ.filter (fun g => 0 < v g)).card : ℝ) := by exact_mod_cast hn
    _ = ∑ g ∈ Finset.univ.filter (fun g => 0 < v g), (1 : ℝ) := by simp
    _ = ∑ g : Fin m, score (v g / a) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases h : 0 < v g
      · simp [h, hscore g h]
      · simp [h, hzero g h]

private theorem preserves_at_next_breakpoint {m L : ℕ} {v : Fin m → ℝ} {a U y z : ℝ}
    (hv : ∀ g, 0 ≤ v g) (ha : 0 < a)
    (hmin : ∀ g, 0 < v g → a ≤ v g)
    (hL : U < a * 2 ^ L) (hay : a ≤ y) (hyz : y ≤ z) (hzU : z ≤ U)
    (hfirst : ∀ q ∈ scaleCandidates v a U L, y ≤ q → z ≤ q) :
    ∀ g, score (v g / y) ≤ score (v g / z) := by
  classical
  intro g
  have hy : 0 < y := ha.trans_le hay
  have hz : 0 < z := hy.trans_le hyz
  have hx : 0 ≤ v g / y := div_nonneg (hv g) hy.le
  by_cases hs : 0 < score (v g / y)
  · have hvg : 0 < v g := by
      have h := hs.trans_le (score_le_value hx)
      exact (div_pos_iff_of_pos_right hy).mp h
    have hlevel := score_level hx hs
    have hthresh (j : ℕ) (b : Bool)
        (he : score (v g / y) = 1 / (2 ^ j * (if b then 3 else 1 : ℝ))) :
        z ≤ v g * 2 ^ j * (if b then 3 else 1 : ℝ) := by
      let t : ℝ := if b then 3 else 1
      have ht : 1 ≤ t := by cases b <;> norm_num [t]
      have hp : 0 < 2 ^ j * t := by positivity
      have hbound : y ≤ v g * 2 ^ j * t := by
        have h := score_le_value hx
        rw [he] at h
        change 1 / (2 ^ j * t) ≤ v g / y at h
        have hh := (div_le_div_iff₀ hp hy).mp h
        simpa [mul_assoc] using hh
      by_cases hU : v g * 2 ^ j * t ≤ U
      · have hj : j < L := by
          apply lt_of_not_ge
          intro hge
          have hpow : (2 : ℝ) ^ L ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hge
          have h₁ : a * (2 : ℝ) ^ L ≤ v g * 2 ^ j :=
            mul_le_mul (hmin g hvg) hpow (by positivity) hvg.le
          have h₂ : v g * 2 ^ j ≤ v g * 2 ^ j * t := le_mul_of_one_le_right (by positivity) ht
          exact (not_le_of_gt hL) (h₁.trans (h₂.trans hU))
        let i : Fin m × Fin L × Bool := (g, ⟨j, hj⟩, b)
        have hm : v g * 2 ^ j * t ∈ scaleCandidates v a U L := by
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
            hay.trans hbound, hU⟩
        exact hfirst _ hm hbound
      · exact hzU.trans (le_of_not_ge hU)
    apply score_ge_level hlevel
    rcases hlevel with ⟨j, h⟩ | ⟨j, h⟩
    · have hb := hthresh j false (by simpa [dyadic] using h)
      rw [h, dyadic]
      apply (div_le_div_iff₀ (by positivity) hz).mpr
      simpa using hb
    · have hb := hthresh j true (by
        simpa only [Bool.true_eq, if_true, thirds, dyadic, div_div] using h)
      rw [h, thirds, dyadic, div_div]
      apply (div_le_div_iff₀ (by positivity) hz).mpr
      simpa [mul_assoc] using hb
  · exact (le_of_not_gt hs).trans (score_nonneg (div_nonneg (hv g) hz.le))

/-- The finite scan finds a greatest admissible scale. In particular the
breakpoint belongs to the feasible side when the score changes there. -/
theorem maximal_scale_by_breakpoints {m n L : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ g, 0 ≤ v g) {a : ℝ} (ha : AdmissibleScale v n a)
    (hmin : ∀ g, 0 < v g → a ≤ v g)
    (hL : bundleValue v Finset.univ / n < a * 2 ^ L) :
    let U := bundleValue v Finset.univ / n
    ∃ y ∈ scaleCandidates v a U L, IsGreatest {y : ℝ | AdmissibleScale v n y} y := by
  classical
  let U := bundleValue v Finset.univ / n
  let candidates := scaleCandidates v a U L
  have hU : U ∈ candidates := by simp [candidates, scaleCandidates]
  have haU : a ≤ U := admissibleScale_le_average hn hv ha
  let eligible := candidates.filter (AdmissibleScale v n)
  have haMem : a ∈ eligible := Finset.mem_filter.mpr
    ⟨by simp [candidates, scaleCandidates], ha⟩
  have hne : eligible.Nonempty := ⟨a, haMem⟩
  let best := eligible.max' hne
  have hbest := Finset.mem_filter.mp (Finset.max'_mem eligible hne)
  refine ⟨best, hbest.1, hbest.2, ?_⟩
  intro y hy
  change AdmissibleScale v n y at hy
  by_cases hay : a ≤ y
  · have hyU : y ≤ U := admissibleScale_le_average hn hv hy
    let right := candidates.filter (fun z => y ≤ z)
    have hr : right.Nonempty := ⟨U, Finset.mem_filter.mpr ⟨hU, hyU⟩⟩
    let z := right.min' hr
    have hz := Finset.mem_filter.mp (Finset.min'_mem right hr)
    have hfirst (q : ℝ) (hq : q ∈ candidates) (hyq : y ≤ q) : z ≤ q :=
      Finset.min'_le right q (Finset.mem_filter.mpr ⟨hq, hyq⟩)
    have hsafe := preserves_at_next_breakpoint hv ha.1 hmin hL hay hz.2 (hfirst U hU hyU) hfirst
    have hzAd : AdmissibleScale v n z :=
      ⟨hy.1.trans_le hz.2, hy.2.trans (Finset.sum_le_sum fun g _ => hsafe g)⟩
    exact hz.2.trans (Finset.le_max' eligible z (Finset.mem_filter.mpr ⟨hz.1, hzAd⟩))
  · exact (le_of_not_ge hay).trans (Finset.le_max' eligible a haMem)

end OnlineMMS.TwoType
