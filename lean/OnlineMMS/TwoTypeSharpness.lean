import OnlineMMS.TwoTypeRationalPolicy
import OnlineMMS.TwoTypePacketWitness
import OnlineMMS.TwoTypePacking
import OnlineMMS.Benchmarks
import Mathlib.Logic.Equiv.Fin.Basic
import OnlineMMS.Asymptotic
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS.TwoType

private theorem dyadic_pos' (j : ℕ) : 0 < dyadic j := by unfold dyadic; positivity

private theorem dyadic_le_half {j : ℕ} (hj : 1 ≤ j) : dyadic j ≤ 1 / 2 := by
  unfold dyadic
  have hp : (2 : ℝ)^1 ≤ 2^j := pow_le_pow_right₀ (by norm_num) hj
  norm_num at hp
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^j)).mpr
  linarith

private def lowCount (j : ℕ) : ℕ := 3 * 2 ^ (j - 1) - 1

private noncomputable def sharpValues (j : ℕ) : Fin (lowCount j + 1) → ℝ :=
  Fin.snoc (fun _ => (3 / 2 - dyadic j) * thirds j) (1 - dyadic j / 4)

private theorem low_count_identity {j : ℕ} (hj : 1 ≤ j) :
    (lowCount j : ℝ) * thirds j = 1 / 2 - thirds j := by
  have hCount : 1 ≤ 3 * 2 ^ (j - 1) := by
    have hp : 0 < (2 : ℕ) ^ (j - 1) := by positivity
    omega
  unfold lowCount thirds dyadic
  rw [Nat.cast_sub hCount]
  push_cast
  have he : (2 : ℝ)^j = 2^(j - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  rw [he]
  field_simp
  ring

private theorem sharp_high_score {j : ℕ} (hj : 1 ≤ j) :
    score (1 - dyadic j / 4) = 1 / 2 := by
  apply score_half_range
  · linarith [dyadic_le_half hj]
  · linarith [dyadic_pos' j]

private theorem sharp_low_score {j : ℕ} (hj : 1 ≤ j) :
    score ((3 / 2 - dyadic j) * thirds j) = thirds j := by
  have hp : 0 < thirds j := by unfold thirds; exact div_pos (dyadic_pos' _) (by norm_num)
  apply score_thirds_range j
  · calc
      thirds j = 1 * thirds j := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [dyadic_le_half hj]) hp.le
  · exact mul_lt_mul_of_pos_right (by linarith [dyadic_pos' j]) hp

private theorem sharp_values_nonneg {j : ℕ} (hj : 1 ≤ j) (g : Fin (lowCount j + 1)) :
    0 ≤ sharpValues j g := by
  refine Fin.lastCases ?_ (fun i => ?_) g
  · simp [sharpValues]
    linarith [dyadic_le_half hj]
  · simp [sharpValues]
    exact mul_nonneg (by linarith [dyadic_le_half hj])
      (div_nonneg (dyadic_pos' j).le (by norm_num))

/-- The score-initialization cutoff has the manuscript's approaching examples. -/
theorem score_cutoff_example {j : ℕ} (hj : 1 ≤ j) :
    (∀ g, 0 ≤ sharpValues j g) ∧
      bundleValue (sharpValues j) Finset.univ =
        7 / 4 - (5 / 4) * dyadic j + (dyadic j)^2 / 3 ∧
      bundleValue (fun g => score (sharpValues j g)) Finset.univ = 1 - thirds j := by
  refine ⟨sharp_values_nonneg hj, ?_, ?_⟩
  · unfold bundleValue
    rw [Fin.sum_univ_castSucc]
    simp only [sharpValues, Fin.snoc_castSucc, Fin.snoc_last, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have he : (lowCount j : ℝ) * ((3 / 2 - dyadic j) * thirds j) =
        (3 / 2 - dyadic j) * (1 / 2 - thirds j) := by
      rw [← low_count_identity hj]
      ring
    rw [he]
    unfold thirds
    ring
  · unfold bundleValue
    rw [Fin.sum_univ_castSucc]
    simp only [sharpValues, Fin.snoc_castSucc, Fin.snoc_last, sharp_high_score hj, sharp_low_score hj,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [low_count_identity hj]
    ring

open Filter
open scoped Topology

/-- The score-deficient examples approach the initialization cutoff from below. -/
theorem score_cutoff_sharp :
    Tendsto (fun j : ℕ => bundleValue (sharpValues j) Finset.univ)
      atTop (𝓝 (7 / 4 : ℝ)) ∧
    ∀ j : ℕ, 1 ≤ j → bundleValue (fun g => score (sharpValues j g)) Finset.univ < 1 := by
  have hzero : Tendsto dyadic atTop (𝓝 0) := by
    have h : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    change Tendsto (fun j : ℕ => 1 / (2 : ℝ)^j) atTop (𝓝 0)
    simpa [div_pow] using h
  constructor
  · have hfun : Tendsto (fun j : ℕ => (7 / 4 : ℝ) - (5 / 4) * dyadic j + (dyadic j)^2 / 3)
        atTop (𝓝 ((7 / 4 : ℝ) - (5 / 4) * 0 + (0 : ℝ)^2 / 3)) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hzero)).add (hzero.pow 2 |>.div_const 3)
    have he : (fun j : ℕ => (7 / 4 : ℝ) - (5 / 4) * dyadic j + (dyadic j)^2 / 3) =ᶠ[atTop]
        (fun j : ℕ => bundleValue (sharpValues j) Finset.univ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      exact (score_cutoff_example hj).2.1.symm
    simpa using hfun.congr' he
  · intro j hj
    rw [(score_cutoff_example hj).2.2]
    have hp : 0 < thirds j := by unfold thirds; exact div_pos (dyadic_pos' j) (by norm_num)
    linarith

private def horizon (j : ℕ) : ℕ := 3 * 2^j
private def ordinaryCount (j : ℕ) : ℕ := horizon j * (lowCount j + 1)

private noncomputable def sharpA (j : ℕ) : Fin (ordinaryCount j + 1) → ℝ :=
  Fin.snoc (fun g => sharpValues j (finProdFinEquiv.symm g).2) 1

private def extra (j : ℕ) : Fin (ordinaryCount j + 1) := Fin.last _

private def sharpB (j : ℕ) (g : Fin (ordinaryCount j + 1)) : ℝ :=
  if g = extra j then 0 else 1

private theorem horizon_pos (j : ℕ) : 0 < horizon j := by unfold horizon; positivity

private theorem sharpA_nonneg {j : ℕ} (hj : 1 ≤ j) (g : Fin (ordinaryCount j + 1)) :
    0 ≤ sharpA j g := by
  refine Fin.lastCases ?_ (fun i => ?_) g
  · norm_num [sharpA]
  · simpa [sharpA] using sharp_values_nonneg hj (finProdFinEquiv.symm i).2

private theorem extra_score (j : ℕ) : score (sharpA j (extra j)) = 1 := by
  have h : score (1 : ℝ) = 1 := by
    unfold score
    norm_num
  simpa [sharpA, extra] using h

/-- The second type has an admissible positive scale on the witness. -/
theorem sharp_policy_B_scale_one (j : ℕ) :
    (horizon j : ℝ) ≤ bundleValue (fun g => score (sharpB j g / 1)) Finset.univ := by
  have hscore : score (1 : ℝ) = 1 := by unfold score; norm_num
  unfold bundleValue
  rw [Fin.sum_univ_castSucc]
  have hordinary (i : Fin (ordinaryCount j)) : sharpB j i.castSucc = 1 := by
    simp [sharpB, extra, Fin.castSucc_ne_last]
  have hlast : sharpB j (Fin.last (ordinaryCount j)) = 0 := by simp [sharpB, extra]
  simp only [hordinary, hlast, div_one, hscore, show score 0 = 0 by simp [score],
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn : horizon j ≤ ordinaryCount j := by
    unfold ordinaryCount
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  exact_mod_cast hn

private theorem original_score_sum {j : ℕ} (hj : 1 ≤ j) :
    bundleValue (fun g => score (sharpA j g)) Finset.univ = (horizon j : ℝ) := by
  unfold bundleValue
  rw [Fin.sum_univ_castSucc]
  have he : ∑ i : Fin (ordinaryCount j), score (sharpA j i.castSucc) =
      ∑ p : Fin (horizon j) × Fin (lowCount j + 1), score (sharpValues j p.2) := by
    apply Fintype.sum_equiv finProdFinEquiv.symm
    intro i
    simp [sharpA]
  rw [he, Fintype.sum_prod_type]
  have hscore := (score_cutoff_example hj).2.2
  change ∑ g, score (sharpValues j g) = 1 - thirds j at hscore
  have hone : (horizon j : ℝ) * thirds j = 1 := by
    unfold horizon thirds dyadic
    push_cast
    field_simp
    ring
  change (∑ _i : Fin (horizon j), (∑ g, score (sharpValues j g))) + score (sharpA j (extra j)) = _
  rw [extra_score, hscore]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [show (horizon j : ℝ) * (1 - thirds j) = horizon j - 1 by rw [mul_sub, mul_one, hone]]

/-- On the sharpness family, the maximal admissible scale for A is exactly one. -/
theorem sharp_policy_max_scale {j : ℕ} (hj : 1 ≤ j) :
    IsGreatest {y : ℝ | 0 < y ∧
      (horizon j : ℝ) ≤ bundleValue (fun g => score (sharpA j g / y)) Finset.univ} 1 := by
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · simp [original_score_sum hj]
  · intro y hy
    by_contra! hy1
    have hh : bundleValue (fun g => score (sharpA j g / y)) Finset.univ <
        bundleValue (fun g => score (sharpA j g)) Finset.univ := by
      apply Finset.sum_lt_sum
      · intro g _
        have hval : 0 ≤ sharpA j g := sharpA_nonneg hj g
        exact score_monotone (div_nonneg hval (by linarith)) (div_le_self hval hy1.le)
      · refine ⟨extra j, Finset.mem_univ _, ?_⟩
        rw [extra_score]
        have hval : sharpA j (extra j) = 1 := by simp [extra, sharpA]
        rw [hval]
        exact (score_le_value (by positivity)).trans_lt ((div_lt_one (by linarith)).mpr hy1)
    have hlow := hy.2
    rw [original_score_sum hj] at hh
    linarith

/-- Each copy of the score-deficient bundle is a part of a feasible MMS partition. -/
theorem sharp_policy_mms_lower {j : ℕ} (hj : 1 ≤ j) :
    bundleValue (sharpValues j) Finset.univ ≤
      maximinShare (sharpA j) (horizon j) (horizon_pos j) := by
  classical
  letI : Nonempty (Fin (horizon j)) := ⟨⟨0, horizon_pos j⟩⟩
  let p : Fin (ordinaryCount j + 1) → Fin (horizon j) :=
    Fin.snoc (fun i => (finProdFinEquiv.symm i).1) ⟨0, horizon_pos j⟩
  apply le_trans _ (partitionMin_le_maximinShare (sharpA j) (horizon_pos j) p)
  apply Finset.le_inf'
  intro t _
  let f : Fin (lowCount j + 1) → Fin (ordinaryCount j + 1) :=
    fun g => (finProdFinEquiv (t, g)).castSucc
  have hf : Function.Injective f := by
    intro a b h
    have h' := finProdFinEquiv.injective (Fin.castSucc_injective _ h)
    exact congrArg Prod.snd h'
  have hsubs : Finset.univ.image f ⊆ Finset.univ.filter (fun g => p g = t) := by
    intro g hg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, f, Fin.snoc_castSucc, Equiv.symm_apply_apply]
  calc
    bundleValue (sharpValues j) Finset.univ = bundleValue (sharpA j) (Finset.univ.image f) := by
      unfold bundleValue
      rw [Finset.sum_image (fun a _ b _ h => hf h)]
      simp only [sharpA, f, Fin.snoc_castSucc, Equiv.symm_apply_apply]
    _ ≤ partitionValue (sharpA j) p t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubs (fun g _ _ => sharpA_nonneg hj g)

/-- If the extra singleton is among the unit-packet candidates, every
least-cost choice for the other type pays exactly one to the first type. -/
theorem sharp_policy_forced_singleton {j : ℕ}
    (scaleB : ℝ) (hb : 0 < scaleB)
    (B : Finset (Fin (ordinaryCount j + 1)))
    (hp : 1 ≤ bundleValue (fun g => score (sharpA j g)) B)
    (hcost : bundleValue (fun g => score (sharpB j g / scaleB)) B ≤
      bundleValue (fun g => score (sharpB j g / scaleB)) {extra j}) :
    B = {extra j} ∧ bundleValue (sharpA j) B = 1 := by
  have hBsub : B ⊆ {extra j} := by
    intro g hg
    apply Finset.mem_singleton.mpr
    apply Classical.byContradiction
    intro hn
    have hv : 0 < sharpB j g / scaleB := by
      rw [sharpB, if_neg hn]
      exact div_pos one_pos hb
    have hsingle : score (sharpB j g / scaleB) ≤ bundleValue (fun g => score (sharpB j g / scaleB)) B :=
      Finset.single_le_sum (fun i _ => score_nonneg (div_nonneg (by
        unfold sharpB
        split_ifs <;> norm_num) hb.le)) hg
    have hz : bundleValue (fun g => score (sharpB j g / scaleB)) {extra j} = 0 := by
      simp [bundleValue, sharpB, score]
    have hc := hsingle.trans (hcost.trans_eq hz)
    exact (not_le_of_gt (score_pos hv)) hc
  have hne : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hp
    norm_num [bundleValue] at hp
  obtain ⟨g, hg⟩ := hne
  have he : g = extra j := Finset.mem_singleton.mp (hBsub hg)
  refine ⟨Finset.Subset.antisymm hBsub ?_, ?_⟩
  · apply Finset.singleton_subset_iff.mpr
    simpa [he] using hg
  · have hEq : B = {extra j} := Finset.Subset.antisymm hBsub
      (Finset.singleton_subset_iff.mpr (by simpa [he] using hg))
    simp [hEq, bundleValue, sharpA, extra]

private theorem sharp_policy_menu {j : ℕ} (hj : 1 ≤ j) :
    ∃ bags : Fin (horizon j - 1 + 1) → Finset (Fin (ordinaryCount j + 1)),
      bags 0 = {extra j} ∧ Pairwise (fun i l => Disjoint (bags i) (bags l)) ∧
      ∀ i, 1 ≤ bundleValue (fun g => score (sharpA j g)) (bags i) := by
  classical
  let R : Finset (Fin (ordinaryCount j + 1)) := Finset.univ.erase (extra j)
  let w := fun g => score (sharpA j g)
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin (ordinaryCount j + 1)))
    w (Finset.mem_univ (extra j))
  change bundleValue w R + score (sharpA j (extra j)) =
    bundleValue w (Finset.univ : Finset (Fin (ordinaryCount j + 1))) at hsum
  rw [extra_score, original_score_sum hj] at hsum
  have hscore : ((horizon j - 1 : ℕ) : ℝ) ≤ bundleValue w R := by
    rw [Nat.cast_sub (by have := horizon_pos j; omega)]
    norm_num
    linarith
  obtain ⟨G⟩ := score_pack (sharpA j) (sharpA_nonneg hj) (horizon j - 1) R hscore
  let B : Fin (horizon j - 1 + 1) → Finset (Fin (ordinaryCount j + 1)) :=
    Fin.cons (α := fun _ => Finset (Fin (ordinaryCount j + 1))) {extra j} G.bag
  have hsep (i : Fin (horizon j - 1)) : Disjoint {extra j} (G.bag i) := by
    apply Finset.disjoint_singleton_left.mpr
    intro hg
    exact (Finset.mem_erase.mp (G.subset i hg)).1 rfl
  refine ⟨B, rfl, ?_, ?_⟩
  · intro i l hil
    revert l
    refine Fin.cases (fun l hil => ?_) (fun i l hil => ?_) i
    · revert hil
      refine Fin.cases (fun hh => False.elim (hh rfl)) (fun l _ => hsep l) l
    · revert hil
      refine Fin.cases (fun _ => (hsep i).symm) (fun l h => ?_) l
      exact G.disjoint (fun he => h (congrArg Fin.succ he))
  · intro i
    refine Fin.cases ?_ G.pays i
    change 1 ≤ bundleValue w {extra j}
    simp [bundleValue, w, extra_score]

open Filter
open scoped Topology

/-- For each claimed fraction above 4/7 there is a family member on which
the all-unit-packet menu containing the extra good forces a smaller first
payment, at A's maximal scale and every positive scale for B. -/
theorem sharp_policy_first_round {ρ : ℝ} (hρ : 4 / 7 < ρ) :
    ∃ j, 1 ≤ j ∧
      (IsGreatest {y : ℝ | 0 < y ∧
        (horizon j : ℝ) ≤ bundleValue (fun g => score (sharpA j g / y)) Finset.univ} 1) ∧
      ∃ bags : Fin (horizon j - 1 + 1) → Finset (Fin (ordinaryCount j + 1)),
        bags 0 = {extra j} ∧ Pairwise (fun i l => Disjoint (bags i) (bags l)) ∧
        (∀ i, 1 ≤ bundleValue (fun g => score (sharpA j g)) (bags i)) ∧
        ∀ b > 0, ∀ i, (∀ l, bundleValue (fun g => score (sharpB j g / b)) (bags i) ≤
          bundleValue (fun g => score (sharpB j g / b)) (bags l)) →
          bundleValue (sharpA j) (bags i) < ρ *
            maximinShare (sharpA j) (horizon j) (horizon_pos j) := by
  have hpos : 0 < ρ := by linarith
  have hLt : (1 : ℝ) / ρ < 7 / 4 := by
    apply (div_lt_iff₀ hpos).mpr
    linarith
  have hlater := score_cutoff_sharp.1.eventually_const_lt hLt
  obtain ⟨j, hj, hhigh⟩ := ((eventually_ge_atTop (1 : ℕ)).and hlater).exists
  obtain ⟨bags, h0, hd, hpay⟩ := sharp_policy_menu hj
  refine ⟨j, hj, sharp_policy_max_scale hj, bags, h0, hd, hpay, ?_⟩
  intro b hb i hmin
  have he := hmin 0
  rw [h0] at he
  rw [(sharp_policy_forced_singleton b hb _ (hpay i) he).2]
  have hp := (div_lt_iff₀ hpos).mp (hhigh.trans_le (sharp_policy_mms_lower hj))
  linarith [mul_comm ρ (maximinShare (sharpA j) (horizon j) (horizon_pos j))]

private def sharpValuesRat (j : ℕ) : Fin (lowCount j + 1) → ℚ :=
  let d : ℚ := 1 / 2 ^ j
  Fin.snoc (fun _ => (3 / 2 - d) * (d / 3)) (1 - d / 4)

private def sharpARat (j : ℕ) : Fin (ordinaryCount j + 1) → ℚ :=
  Fin.snoc (fun g => sharpValuesRat j (finProdFinEquiv.symm g).2) 1

private def sharpBRat (j : ℕ) (g : Fin (ordinaryCount j + 1)) : ℚ :=
  if g = extra j then 0 else 1

private def sharpValuationsRat (j : ℕ) (t : Fin 2) : Fin (ordinaryCount j + 1) → ℚ :=
  if t = 0 then sharpARat j else sharpBRat j

private theorem sharpARat_cast (j : ℕ) (g : Fin (ordinaryCount j + 1)) :
    (sharpARat j g : ℝ) = sharpA j g := by
  refine Fin.lastCases ?_ (fun i => ?_) g
  · simp [sharpARat, sharpA]
  · simp only [sharpARat, sharpA, Fin.snoc_castSucc]
    generalize (finProdFinEquiv.symm i).2 = x
    refine Fin.lastCases ?_ (fun z => ?_) x
    · simp [sharpValuesRat, sharpValues, dyadic]
    · simp [sharpValuesRat, sharpValues, dyadic, thirds]

private theorem sharpBRat_cast (j : ℕ) (g : Fin (ordinaryCount j + 1)) :
    (sharpBRat j g : ℝ) = sharpB j g := by
  by_cases h : g = extra j <;> simp [sharpBRat, sharpB, h]

private theorem sharpValuationsRat_nonneg {j : ℕ} (hj : 1 ≤ j) (t : Fin 2)
    (g : Fin (ordinaryCount j + 1)) : 0 ≤ sharpValuationsRat j t g := by
  unfold sharpValuationsRat
  split
  · have hr := sharpA_nonneg hj g
    rw [← sharpARat_cast] at hr
    exact_mod_cast hr
  · unfold sharpBRat
    split <;> norm_num

private theorem sharp_choice_is_extra {j : ℕ} (hj : 1 ≤ j) :
    let v := sharpValuationsRat j
    let y (t : Fin 2) := rationalScale (v t) (horizon j)
    let tag (t : Fin 2) (g : Fin (ordinaryCount j + 1)) :=
      roundedTagRat (scaleScanLimit (v t)) (v t g / y t)
    packetChoice y tag (horizon j) Finset.univ 0 = {extra j} := by
  classical
  let v := sharpValuationsRat j
  let y (t : Fin 2) := rationalScale (v t) (horizon j)
  let tag (t : Fin 2) (g : Fin (ordinaryCount j + 1)) :=
    roundedTagRat (scaleScanLimit (v t)) (v t g / y t)
  have hn := horizon_pos j
  have hx (t : Fin 2) (g : Fin (ordinaryCount j + 1)) :
      score ((v t g : ℝ) / (y t : ℝ)) = (tag t g).elim 0 PacketLevel.weight :=
    (rationalScale_tag_correct (v t) (sharpValuationsRat_nonneg hj t) hn g).symm
  have hA : (fun g => (v 0 g : ℝ)) = sharpA j := by
    funext g
    exact sharpARat_cast j g
  have hB : (fun g => (v 1 g : ℝ)) = sharpB j := by
    funext g
    exact sharpBRat_cast j g
  have hyA : (y 0 : ℝ) = 1 := by
    have h := rationalScale_spec (v 0) (sharpValuationsRat_nonneg hj 0) hn
    rw [hA] at h
    have hmax : IsGreatest {u : ℝ | AdmissibleScale (sharpA j) (horizon j) u} 1 :=
      sharp_policy_max_scale hj
    rcases h with ⟨_, he⟩ | h
    · exact (he _ hmax.1).elim
    · exact h.unique hmax
  have hyB : 0 < (y 1 : ℝ) := by
    have h := rationalScale_spec (v 1) (sharpValuationsRat_nonneg hj 1) hn
    rw [hB] at h
    have ha : AdmissibleScale (sharpB j) (horizon j) 1 := ⟨one_pos, sharp_policy_B_scale_one j⟩
    rcases h with ⟨_, he⟩ | h
    · exact (he _ ha).elim
    · exact h.1.1
  let a (g : Fin (ordinaryCount j + 1)) := score (sharpA j g)
  let B := preparedMenu (tag 0) Finset.univ (horizon j)
  have haTag (g : Fin (ordinaryCount j + 1)) :
      a g = (tag 0 g).elim 0 PacketLevel.weight := by
    have h := hx 0 g
    rw [congrFun hA g, hyA, div_one] at h
    exact h
  have hExtra : tag 0 (extra j) = some .unit := by
    have he := (extra_score j).symm.trans (haTag (extra j))
    cases ht : tag 0 (extra j) with
    | none => simp [ht] at he
    | some level =>
      cases level with
      | unit => rfl
      | half i =>
        simp only [ht, Option.elim_some, PacketLevel.weight] at he
        have hp : dyadic (i + 1) ≤ 1 / 2 := by
          unfold dyadic
          apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
          simpa using (show (2 : ℝ) ^ 1 ≤ 2 ^ (i + 1) from
            pow_le_pow_right₀ (by norm_num) (by omega))
        linarith
      | third i =>
        simp only [ht, Option.elim_some, PacketLevel.weight] at he
        have hp : dyadic i ≤ 1 := by
          unfold dyadic
          apply (div_le_one₀ (by positivity)).mpr
          exact one_le_pow₀ (by norm_num)
        unfold thirds at he
        linarith
  have hnon (g : Fin (ordinaryCount j + 1)) : 0 ≤ a g := score_nonneg (sharpA_nonneg hj g)
  have hsum : bundleValue a Finset.univ = horizon j := original_score_sum hj
  have heB : {extra j} ∈ B := preparedMenu_offers_unit (tag 0) Finset.univ a haTag hnon hsum
    (Finset.mem_univ _) hExtra
  have hmenu := preparedMenu_spec (tag 0) Finset.univ a haTag hsum.ge
  let cost (G : Finset (Fin (ordinaryCount j + 1))) :=
    ∑ g ∈ G, (tag (otherType 0) g).elim 0 PacketLevel.weightRat
  have hcost (G : Finset (Fin (ordinaryCount j + 1))) :
      (cost G : ℝ) = bundleValue (fun g => score (sharpB j g / (y 1 : ℝ))) G := by
    unfold cost bundleValue
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    have ht : otherType (0 : Fin 2) = 1 := by decide
    rw [ht, ← congrFun hB g, hx]
    cases tag 1 g <;> simp
  have hr : ¬ horizon j ≤ 1 := by
    have hp : 0 < (2 : ℕ)^j := by positivity
    unfold horizon
    omega
  have hy : 0 < y 0 := by
    have h : (0 : ℝ) < (y 0 : ℝ) := by rw [hyA]; norm_num
    exact_mod_cast h
  change packetChoice y tag (horizon j) Finset.univ 0 = {extra j}
  unfold packetChoice
  rw [if_neg hr, if_neg (not_le_of_gt hy)]
  change (B.argmin cost).getD ∅ = {extra j}
  cases he : B.argmin cost with
  | none =>
    have h := List.argmin_eq_none.mp he
    rw [h] at heB
    simp at heB
  | some G =>
    have h := List.argmin_eq_some_iff.mp he
    have hp := (hmenu.2.2 G h.1).2.1
    have hle : bundleValue (fun g => score (sharpB j g / (y 1 : ℝ))) G ≤
        bundleValue (fun g => score (sharpB j g / (y 1 : ℝ))) {extra j} := by
      rw [← hcost G, ← hcost {extra j}]
      exact_mod_cast h.2.1 _ heB
    exact (sharp_policy_forced_singleton (y 1 : ℝ) hyB G hp hle).1

/-- The executable maximum-scale merging rule cannot guarantee more than
four sevenths, already on the first move of the rational witness family. -/
theorem rationalPacketPolicy_sharp {ρ : ℝ} (hρ : 4 / 7 < ρ) :
    ∃ (m n : ℕ) (hn : 0 < n) (v : Fin 2 → Fin m → ℚ),
      (∀ t g, 0 ≤ v t g) ∧
      ¬ (rationalPacketPolicy v n).Guarantees (fun t g => (v t g : ℝ))
        (fun t => ρ * maximinShare (fun g => (v t g : ℝ)) n hn) Finset.univ := by
  have hpos : 0 < ρ := by linarith
  have hlt : (1 : ℝ) / ρ < 7 / 4 := (div_lt_iff₀ hpos).mpr (by linarith)
  obtain ⟨j, hj, hval⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (score_cutoff_sharp.1.eventually_const_lt hlt)).exists
  let n := horizon j
  let v := sharpValuationsRat j
  let y (t : Fin 2) := rationalScale (v t) n
  let tag (t : Fin 2) (g : Fin (ordinaryCount j + 1)) :=
    roundedTagRat (scaleScanLimit (v t)) (v t g / y t)
  have hn : 0 < n := horizon_pos j
  refine ⟨ordinaryCount j + 1, n, hn, v, sharpValuationsRat_nonneg hj, ?_⟩
  intro h
  have hA : (fun g => (v 0 g : ℝ)) = sharpA j := by
    funext g
    exact sharpARat_cast j g
  have hp : ρ * maximinShare (fun g => (v 0 g : ℝ)) n hn ≤
      bundleValue (fun g => (v 0 g : ℝ)) (packetChoice y tag n Finset.univ 0) := by
    exact rationalPacketPolicy_first_payment v hn _ h 0
  rw [hA, sharp_choice_is_extra hj] at hp
  have he : bundleValue (sharpA j) {extra j} = 1 := by simp [bundleValue, sharpA, extra]
  rw [he] at hp
  have hh := (div_lt_iff₀ hpos).mp (hval.trans_le (sharp_policy_mms_lower hj))
  linarith [mul_comm ρ (maximinShare (sharpA j) n hn)]

/-- Four sevenths is the exact worst-case guarantee of this particular
policy across all horizons and explicit rational inputs. -/
theorem rationalPacketPolicy_exact_guarantee :
    IsGreatest {ρ : ℝ | ∀ (m n : ℕ) (hn : 0 < n) (v : Fin 2 → Fin m → ℚ),
      (∀ t g, 0 ≤ v t g) →
      (rationalPacketPolicy v n).Guarantees (fun t g => (v t g : ℝ))
        (fun t => ρ * maximinShare (fun g => (v t g : ℝ)) n hn) Finset.univ} (4 / 7) := by
  constructor
  · intro _ _ hn v hv
    exact rationalPacketPolicy_guarantees v hv hn
  · intro ρ h
    apply le_of_not_gt
    intro hρ
    obtain ⟨m, n, hn, v, hv, hbad⟩ := rationalPacketPolicy_sharp hρ
    exact hbad (h m n hn v hv)

end OnlineMMS.TwoType
