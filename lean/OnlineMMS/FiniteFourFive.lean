import OnlineMMS.FiniteThree
import OnlineMMS.FiniteResidual
import OnlineMMS.FinitePadding

namespace OnlineMMS

private def remainingRows {m n : ℕ} (R : Finset (Fin m)) (rows : Fin m → Fin n)
    (D : Finset (Fin n)) : Finset (Fin m) := R.filter (fun g => rows g ∉ D)

private theorem remainingRows_remove {m n : ℕ} (R : Finset (Fin m)) (rows : Fin m → Fin n)
    (D : Finset (Fin n)) (i : Fin n) :
    remainingRows R rows D \ R.filter (fun g => rows g = i) =
      remainingRows R rows (insert i D) := by
  ext g
  simp only [remainingRows,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_insert]
  tauto

private theorem remainingRows_single {m n : ℕ} (R : Finset (Fin m)) (rows : Fin m → Fin n)
    (i : Fin n) :
    R \ R.filter (fun g => rows g = i) = remainingRows R rows {i} := by
  ext g
  simp only [Finset.mem_sdiff,remainingRows,Finset.mem_filter,Finset.mem_singleton]
  tauto

private theorem next_row {n : ℕ} (score : Fin n → ℝ) (D : Finset (Fin n)) {r : ℕ}
    (hc : (Finset.univ \ D).card = r + 1) :
    ∃ i : Fin n, i ∉ D ∧ (∀ j ∉ D, score i ≤ score j) ∧
      (Finset.univ \ insert i D).card = r := by
  classical
  let U := Finset.univ \ D
  have hU : U.Nonempty := Finset.card_pos.mp (by rw [show U.card = _ from hc]; omega)
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image U score hU
  refine ⟨i,(Finset.mem_sdiff.mp hi).2,fun j hj => hmin j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩),?_⟩
  have he : Finset.univ \ insert i D = U.erase i := by
    ext j
    simp [U,Finset.mem_sdiff,and_comm]
  rw [he,Finset.card_erase_of_mem hi,show U.card = _ from hc]
  omega

private theorem extend_ordered {n : ℕ} (score : Fin n → ℝ) (D : Finset (Fin n)) (i : Fin n)
    (hD : ∀ x ∈ D, ∀ y ∉ D, score x ≤ score y)
    (hmin : ∀ y ∉ D, score i ≤ score y) :
    ∀ x ∈ insert i D, ∀ y ∉ insert i D, score x ≤ score y := by
  intro x hx y hy
  have hy' : y ∉ D := fun h => hy (Finset.mem_insert_of_mem h)
  rcases Finset.mem_insert.mp hx with h | h
  · rw [h]
    exact hmin y hy'
  · exact hD x h y hy'

private theorem row_kept_subset {m n : ℕ} (R : Finset (Fin m)) (rows : Fin m → Fin n)
    (D : Finset (Fin n)) {a : Fin n} (ha : a ∉ D) :
    R.filter (fun g => rows g = a) ⊆ remainingRows R rows D := by
  intro g hg
  obtain ⟨hR,he⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hR,he ▸ ha⟩

/-- The four-arrival continuation for a particular first-type revelation. -/
theorem four_arrival_first_choice {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (q : Fin 2 → ℝ) (hq : ∀ t, 0 ≤ q t)
    (h : ∀ t, HasPaymentPartition (v t) R 4 (q t)) (a : Fin 2) :
    ∃ (G : Finset (Fin m)) (p : Policy m 2 3), G ⊆ R ∧
      q a ≤ bundleValue (v a) G ∧
      p.Guarantees v (orientedTarget q (9/10) (3/4) a) (R \ G) := by
  classical
  obtain ⟨b,hba,hcases⟩ := two_type_alternative a
  obtain ⟨rows,hrows⟩ := h a
  obtain ⟨cols,hcols⟩ := h b
  let w := normalizedColumnWeight (v b) R cols
  let score := fun i : Fin 4 => bundleValue w (R.filter (fun g => rows g = i))
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) score Finset.univ_nonempty
  let G := R.filter (fun g => rows g = i)
  let D : Finset (Fin 4) := {i}
  let U := remainingRows R rows D
  have hU : R \ G = U := remainingRows_single R rows i
  have hcount : (Finset.univ \ D).card = 3 := by
    rw [Finset.card_sdiff (Finset.subset_univ D)]
    simp [D]
  have hA3 : HasPaymentPartition (v a) U 3 (q a) :=
    retained_rows_partition (v a) R rows D (by decide) hcount (fun j _ => hrows j)
  have hB3 : HasPaymentPartition (v b) U 3 (q b * (3/4)) := by
    simpa [U,D,remainingRows] using residual_one_row_three_quarters
      (v b) (hv b) R rows cols i (by decide : 2 ≤ 3) (hq b) hcols
      (fun j => hmin j (Finset.mem_univ _))
  let target := orientedTarget q (9/10) (3/4) a
  have hUa : target a ≤ q a := by simp [target,orientedTarget]; linarith [hq a]
  have hUb : target b = (3/4) * q b := by simp [target,orientedTarget,hba]
  have hcont : ∃ p : Policy m 2 3, p.Guarantees v target U := by
    apply policy_step_of_choices
    intro t
    rcases hcases t with ht | ht
    · subst t
      obtain ⟨j,hj,hjmin,hcount'⟩ := next_row score D (show (Finset.univ \ D).card = 2+1 from hcount)
      let J := R.filter (fun g => rows g = j)
      let W := remainingRows R rows (insert j D)
      have hW : U \ J = W := remainingRows_remove R rows D j
      have hSortD : ∀ x ∈ D, ∀ y ∉ D, score x ≤ score y := by
        intro x hx y _
        have ex : x = i := Finset.mem_singleton.mp hx
        simpa [ex] using hmin y (Finset.mem_univ _)
      have hSorted := extend_ordered score D j hSortD hjmin
      have hA2 : HasPaymentPartition (v a) W 2 (q a) :=
        retained_rows_partition (v a) R rows _ (by decide) hcount' (fun j _ => hrows j)
      have hB2 : HasPaymentPartition (v b) W 2 (q b * (4/5)) := by
        have hh := residual_rows_for_other_type (v b) (hv b) R rows cols (insert j D)
          (by decide : 0 < 2) hcount' (hq b) hcols hSorted
        norm_num [W,remainingRows] at hh ⊢
        exact hh
      obtain ⟨p,hp⟩ := two_arrival_policy_of_partitions v W target (by
        intro z
        rcases hcases z with hz | hz
        · subst z
          exact paymentPartition_mono hUa hA2
        · subst z
          apply paymentPartition_mono _ hB2
          rw [hUb]
          nlinarith [hq b])
      exact ⟨J,p,row_kept_subset R rows D hj,hUa.trans (hrows j),hW.symm ▸ hp⟩
    · subst t
      let q' : Fin 2 → ℝ := fun t => if t = a then q t else q t * (3/4)
      have hpart (t : Fin 2) : HasPaymentPartition (v t) U 3 (q' t) := by
        rcases hcases t with ht | ht
        · subst t
          simpa [q'] using hA3
        · subst t
          simpa [q',hba] using hB3
      obtain ⟨J,p,hJ,hpay,hp⟩ := three_arrival_first_choice v hv U q' hpart b
      have he (t : Fin 2) : orientedTarget q' 1 (9/10) b t = target t := by
        rcases hcases t with ht | ht <;> subst t <;>
          simp [target,q',orientedTarget,hba,hba.symm,mul_comm]
      refine ⟨J,p,hJ,?_,hp.mono (fun t => (he t).ge)⟩
      simpa [target,q',orientedTarget,hba,mul_comm] using hpay
  obtain ⟨p,hp⟩ := hcont
  exact ⟨G,p,Finset.filter_subset _ _,hrows _,hU.symm ▸ hp⟩

/-- Give the initial type its least remaining row until the other type
arrives, then apply the supplied continuation rule. -/
private theorem initial_type_prefix {m n : ℕ} (v : Fin 2 → Fin m → ℝ) (R : Finset (Fin m))
    (rows : Fin m → Fin n) (score : Fin n → ℝ) (a b : Fin 2)
    (htypes : ∀ t, t = a ∨ t = b) (target : Fin 2 → ℝ)
    (hrow : ∀ i, target a ≤ bundleValue (v a) (R.filter (fun g => rows g = i)))
    (switch : ∀ r ≤ 3, ∀ D : Finset (Fin n), (Finset.univ \ D).card = r+1 →
      (∀ i ∈ D, ∀ j ∉ D, score i ≤ score j) →
      ∃ (G : Finset (Fin m)) (p : Policy m 2 r), G ⊆ remainingRows R rows D ∧
        target b ≤ bundleValue (v b) G ∧
        p.Guarantees v target (remainingRows R rows D \ G)) :
    ∀ r ≤ 4, ∀ D : Finset (Fin n), (Finset.univ \ D).card = r →
      (∀ i ∈ D, ∀ j ∉ D, score i ≤ score j) →
      ∃ p : Policy m 2 r, p.Guarantees v target (remainingRows R rows D) := by
  intro r
  induction r with
  | zero => intro _ _ _ _; exact ⟨.done,trivial⟩
  | succ r ih =>
    intro hr D hc hd
    apply policy_step_of_choices
    intro t
    rcases htypes t with ht | ht
    · subst t
      obtain ⟨i,hi,hmin,hsize⟩ := next_row score D hc
      obtain ⟨p,hp⟩ := ih (by omega) (insert i D) hsize (extend_ordered score D i hd hmin)
      exact ⟨_,p,row_kept_subset R rows D hi,hrow i,(remainingRows_remove R rows D i).symm ▸ hp⟩
    · subst t
      exact switch r (by omega) D hc hd

/-- The five-arrival continuation with the first type already revealed. -/
theorem five_arrival_first_choice {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (q : Fin 2 → ℝ) (hq : ∀ t, 0 ≤ q t)
    (h : ∀ t, HasPaymentPartition (v t) R 5 (q t)) (a : Fin 2) :
    ∃ (G : Finset (Fin m)) (p : Policy m 2 4), G ⊆ R ∧
      q a ≤ bundleValue (v a) G ∧
      p.Guarantees v (orientedTarget q (3/4) (27/40) a) (R \ G) := by
  classical
  obtain ⟨b,hba,hcases⟩ := two_type_alternative a
  obtain ⟨rows,hrows⟩ := h a
  obtain ⟨cols,hcols⟩ := h b
  let w := normalizedColumnWeight (v b) R cols
  let score := fun i : Fin 5 => bundleValue w (R.filter (fun g => rows g = i))
  let target := orientedTarget q (3/4) (27/40) a
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 5)) score Finset.univ_nonempty
  let G := R.filter (fun g => rows g = i)
  let D : Finset (Fin 5) := {i}
  have hcount : (Finset.univ \ D).card = 4 := by
    rw [Finset.card_sdiff (Finset.subset_univ D)]
    simp [D]
  have hSortD : ∀ x ∈ D, ∀ y ∉ D, score x ≤ score y := by
    intro x hx y _
    have he : x = i := Finset.mem_singleton.mp hx
    simpa [he] using hmin y (Finset.mem_univ _)
  have hFa : target a = (3/4)*q a := by simp [target,orientedTarget]
  have hFb : target b = (27/40)*q b := by simp [target,orientedTarget,hba]
  have hpayrow (j : Fin 5) : target a ≤ bundleValue (v a) (R.filter (fun g => rows g=j)) := by
    rw [hFa]
    linarith [hrows j,hq a]
  have hSwitch : ∀ r ≤ 3, ∀ D : Finset (Fin 5), (Finset.univ \ D).card = r+1 →
      (∀ i ∈ D, ∀ j ∉ D, score i ≤ score j) →
      ∃ (G : Finset (Fin m)) (p : Policy m 2 r), G ⊆ remainingRows R rows D ∧
        target b ≤ bundleValue (v b) G ∧
        p.Guarantees v target (remainingRows R rows D \ G) := by
    intro r hrr D hc hsorted
    let U := remainingRows R rows D
    have hA : HasPaymentPartition (v a) U (r+1) (q a) :=
      retained_rows_partition (v a) R rows D (by omega) hc (fun j _ => hrows j)
    have hB : HasPaymentPartition (v b) U (r+1)
        (q b * (5 / (5 + ((r + 1 : ℕ) : ℝ) - 1))) :=
      residual_rows_for_other_type (v b) (hv b) R rows cols D (by omega) hc (hq b) hcols hsorted
    let q' (β : ℝ) (t : Fin 2) := if t = a then q t else q t * β
    have hpart {β : ℝ} (hB' : HasPaymentPartition (v b) U (r+1) (q b * β)) (t : Fin 2) :
        HasPaymentPartition (v t) U (r+1) (q' β t) := by
      rcases hcases t with ht | ht
      · subst t
        simpa [q'] using hA
      · subst t
        simpa [q',hba] using hB'
    interval_cases r
    · have hval := paymentPartition_total hB
      norm_num at hval
      refine ⟨U,.done,Finset.Subset.refl _,?_,trivial⟩
      rw [hFb]
      linarith [hq b]
    · have hB' : HasPaymentPartition (v b) U 2 (q b * (5/6)) := by
        norm_num at hB
        exact hB
      obtain ⟨p,hp⟩ := two_arrival_policy_of_partitions v U (q' (5/6)) (hpart hB')
      have hle (t : Fin 2) : target t ≤ q' (5/6) t := by
        rcases hcases t with ht | ht
        · subst t
          rw [hFa]
          simp [q']
          linarith [hq a]
        · subst t
          rw [hFb]
          simp [q',hba]
          nlinarith [hq b]
      have hp' := hp.mono hle
      cases p with
      | step bs next => exact ⟨bs b,next b,hp' b⟩
    · have hB' : HasPaymentPartition (v b) U 3 (q b * (5/7)) := by
        norm_num at hB
        exact hB
      obtain ⟨J,p,hJ,hpay,hcont⟩ := three_arrival_first_choice v hv U
        (q' (5/7)) (hpart hB') b
      refine ⟨J,p,hJ,?_,hcont.mono ?_⟩
      · rw [hFb]
        simp [q',hba] at hpay
        linarith [hq b]
      · intro t
        rcases hcases t with ht | ht
        · subst t
          rw [hFa]
          simp [orientedTarget,q',hba.symm]
          linarith [hq a]
        · subst t
          rw [hFb]
          simp [orientedTarget,q',hba]
          nlinarith [hq b]
    · have hD1 : D.card = 1 := by
        have hh := Finset.card_sdiff (Finset.subset_univ D)
        simp only [Finset.card_univ,Fintype.card_fin,hc] at hh
        have hle := Finset.card_le_univ D
        simp only [Fintype.card_fin] at hle
        omega
      obtain ⟨z,hDz⟩ := Finset.card_eq_one.mp hD1
      have hmin' (y : Fin 5) : score z ≤ score y := by
        by_cases hy : y = z
        · simp [hy]
        · exact hsorted z (by simp [hDz]) y (by simpa [hDz] using hy)
      have hB' : HasPaymentPartition (v b) U 4 (q b * (3/4)) := by
        simpa [U,remainingRows,hDz] using residual_one_row_three_quarters (v b) (hv b)
          R rows cols z (by decide : 2 ≤ 4) (hq b) hcols hmin'
      have hq' (t : Fin 2) : 0 ≤ q' (3/4) t := by
        unfold q'
        split
        · exact hq t
        · exact mul_nonneg (hq t) (by norm_num)
      obtain ⟨J,p,hJ,hpay,hcont⟩ := four_arrival_first_choice v hv U (q' (3/4))
        hq' (hpart hB') b
      refine ⟨J,p,hJ,?_,hcont.mono ?_⟩
      · rw [hFb]
        simp [q',hba] at hpay
        linarith [hq b]
      · intro t
        rcases hcases t with ht | ht
        · subst t
          rw [hFa]
          simp [orientedTarget,q',hba.symm]
        · subst t
          rw [hFb]
          simp [orientedTarget,q',hba]
          ring_nf
          exact le_rfl
  obtain ⟨p,hp⟩ := initial_type_prefix v R rows score a b hcases target hpayrow hSwitch
    4 (by decide) D hcount hSortD
  exact ⟨G,p,Finset.filter_subset _ _,hrows i,(remainingRows_single R rows i).symm ▸ hp⟩

private theorem combine_oriented_choices {m r : ℕ} (v : Fin 2 → Fin m → ℝ)
    (R : Finset (Fin m)) (q : Fin 2 → ℝ) (hq : ∀ t, 0 ≤ q t)
    {c a b : ℝ} (hca : c ≤ a) (hcb : c ≤ b) (hc : c ≤ 1)
    (step : ∀ first, ∃ (G : Finset (Fin m)) (p : Policy m 2 r), G ⊆ R ∧
      q first ≤ bundleValue (v first) G ∧
      p.Guarantees v (orientedTarget q a b first) (R \ G)) :
    ∃ p : Policy m 2 (r+1), p.Guarantees v (fun t => c * q t) R := by
  apply policy_step_of_choices
  intro first
  obtain ⟨G,p,hG,hpay,hp⟩ := step first
  have hinitial : c * q first ≤ q first := by
    calc
      _ ≤ 1 * q first := mul_le_mul_of_nonneg_right hc (hq first)
      _ = _ := one_mul _
  refine ⟨G,p,hG,hinitial.trans hpay,hp.mono ?_⟩
  intro t
  unfold orientedTarget
  split
  · exact mul_le_mul_of_nonneg_right hca (hq t)
  · exact mul_le_mul_of_nonneg_right hcb (hq t)

theorem four_arrival_policy_of_partitions {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (q : Fin 2 → ℝ)
    (hq : ∀ t, 0 ≤ q t) (h : ∀ t, HasPaymentPartition (v t) R 4 (q t)) :
    ∃ p : Policy m 2 4, p.Guarantees v (fun t => (3/4)*q t) R :=
  combine_oriented_choices v R q hq (by norm_num) (by norm_num) (by norm_num)
    (four_arrival_first_choice v hv R q hq h)

theorem five_arrival_policy_of_partitions {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (q : Fin 2 → ℝ)
    (hq : ∀ t, 0 ≤ q t) (h : ∀ t, HasPaymentPartition (v t) R 5 (q t)) :
    ∃ p : Policy m 2 5, p.Guarantees v (fun t => (27/40)*q t) R :=
  combine_oriented_choices v R q hq (by norm_num) (by norm_num) (by norm_num)
    (five_arrival_first_choice v hv R q hq h)

theorem alpha_two_types_four_bounds : (3/4 : ℝ) ≤ alphaHorizonMMS 2 4 (by decide) ∧
    alphaHorizonMMS 2 4 (by decide) ≤ 9/10 := by
  constructor
  · apply le_horizonFactor_of_policies _ (by decide) (show (3 / 4 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    intro m v hv
    exact four_arrival_policy_of_partitions v hv Finset.univ
      (fun t => maximinShare (v t) 4 (by decide))
      (fun t => maximinShare_nonnegative (v t) (hv t) (by decide))
      (fun t => paymentPartition_of_mms (v t) (by decide))
  · rw [← alpha_two_types_three_arrivals]
    exact alpha_horizon_mms_padding (by decide : 0 < 3)

theorem alpha_two_types_five_bounds : (27/40 : ℝ) ≤ alphaHorizonMMS 2 5 (by decide) ∧
    alphaHorizonMMS 2 5 (by decide) ≤ 9/10 := by
  constructor
  · apply le_horizonFactor_of_policies _ (by decide) (show (27 / 40 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    intro m v hv
    exact five_arrival_policy_of_partitions v hv Finset.univ
      (fun t => maximinShare (v t) 5 (by decide))
      (fun t => maximinShare_nonnegative (v t) (hv t) (by decide))
      (fun t => paymentPartition_of_mms (v t) (by decide))
  · exact (alpha_horizon_mms_padding (by decide : 0 < 4)).trans alpha_two_types_four_bounds.2

/-- The guarantee transfer when approximate partitions are supplied by an
external approximation algorithm. -/
theorem oriented_approximate_partition_transfer {m n : ℕ} {v : Fin 2 → Fin m → ℝ}
    {R : Finset (Fin m)} {p : Policy m 2 n} (first : Fin 2)
    {q μ : Fin 2 → ℝ} {ε a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (happrox : ∀ t, (1-ε) * μ t ≤ q t)
    (hp : p.Guarantees v (orientedTarget q a b first) R) :
    p.Guarantees v (fun t => (1-ε) * orientedTarget μ a b first t) R := by
  apply hp.mono
  intro t
  unfold orientedTarget
  split
  · calc
      (1-ε) * (a * μ t) = a * ((1-ε) * μ t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (happrox t) ha
  · calc
      (1-ε) * (b * μ t) = b * ((1-ε) * μ t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (happrox t) hb

end OnlineMMS
