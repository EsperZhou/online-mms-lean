import OnlineMMS.FinitePartitions
import OnlineMMS.BaselineBag
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

/-- Sum the parts whose labels lie in a specified set. -/
theorem selected_parts_sum {m n : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    (p : Fin m → Fin n) (D : Finset (Fin n)) :
    (∑ j ∈ D, bundleValue v (R.filter (fun g => p g = j))) =
      bundleValue v (R.filter (fun g => p g ∈ D)) := by
  classical
  unfold bundleValue
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem paymentPartition_addPart {m n : ℕ} (v : Fin m → ℝ)
    (R G : Finset (Fin m)) (hsub : G ⊆ R) {q : ℝ} (hG : q ≤ bundleValue v G)
    (hRest : HasPaymentPartition v (R \ G) n q) :
    HasPaymentPartition v R (n+1) q := by
  classical
  obtain ⟨p,hp⟩ := hRest
  let f : Fin m → Fin (n+1) := fun g => if g ∈ G then Fin.last n else (p g).castSucc
  refine ⟨f,fun j => Fin.lastCases
    (motive := fun j => q ≤ bundleValue v (R.filter fun g => f g = j)) ?_ (fun i => ?_) j⟩
  · have he : R.filter (fun g => f g = Fin.last n) = G := by
      ext g
      by_cases hg : g ∈ G
      · simp [f,hg,hsub hg]
      · simp [f,hg,Fin.castSucc_ne_last]
    change q ≤ bundleValue v (R.filter (fun g => f g = Fin.last n))
    rwa [he]
  · have he : R.filter (fun g => f g = i.castSucc) =
        (R \ G).filter (fun g => p g = i) := by
      ext g
      by_cases hg : g ∈ G
      · simp [f,hg,(Fin.castSucc_ne_last i).symm]
      · simp [f,hg]
    change q ≤ bundleValue v (R.filter (fun g => f g = i.castSucc))
    rw [he]
    exact hp _

/-- A target-valued singleton or a threshold-crossing bag of value at most
twice the threshold. -/
theorem bounded_target_bag {m : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    {q : ℝ} (hq : 0 < q) (hc : ∀ g ∈ R, v g ≤ 2*q) (hv : q ≤ bundleValue v R) :
    ∃ G ⊆ R, q ≤ bundleValue v G ∧ bundleValue v G ≤ 2*q := by
  by_cases hlarge : ∃ g ∈ R, q ≤ v g
  · obtain ⟨g,hg,hval⟩ := hlarge
    exact ⟨{g},Finset.singleton_subset_iff.mpr hg,by simpa [bundleValue],by simpa [bundleValue] using hc g hg⟩
  · have hs (g : Fin m) (hg : g ∈ R) : v g < q :=
      lt_of_not_ge (fun h => hlarge ⟨g,hg,h⟩)
    obtain ⟨G,hG,_,hval,hcap,_⟩ := exists_crossing_bag
      (fun _ : Fin 1 => v) R Finset.univ hq (fun _ _ => hs) ⟨0,Finset.mem_univ _,hv⟩
    obtain ⟨_,_,hval⟩ := hval
    exact ⟨G,hG,hval,hcap 0 (Finset.mem_univ _)⟩

/-- Greedy filling reaches the requested number of parts from the
manuscript's mass and item-size bounds. -/
theorem partition_from_bounded_mass {m r : ℕ} (v : Fin m → ℝ)
    (R : Finset (Fin m)) (hr : 0 < r) {q : ℝ} (hq : 0 < q)
    (hc : ∀ g ∈ R, v g ≤ 2*q)
    (hm : (2*(r : ℝ)-1)*q ≤ bundleValue v R) :
    HasPaymentPartition v R r q := by
  induction r generalizing R with
  | zero => omega
  | succ r ih =>
    by_cases hzero : r = 0
    · subst r
      refine ⟨fun _ => 0,fun j => ?_⟩
      have h : j = 0 := Fin.ext (by have hi := j.isLt; simp at hi; omega)
      norm_num at hm
      simpa [h] using hm
    · have hr' : 0 < r := by omega
      have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr'
      have htot : q ≤ bundleValue v R := by
        have hh : q ≤ (2*((r + 1 : ℕ) : ℝ)-1)*q := by
          push_cast
          nlinarith
        exact hh.trans hm
      obtain ⟨G,hG,hpay,hcost⟩ := bounded_target_bag v R hq hc htot
      have hleft : (2*(r : ℝ)-1)*q ≤ bundleValue v (R \ G) := by
        have hs := bundleValue_sdiff v hG
        push_cast at hm
        linarith [show (2 * ((r : ℝ) + 1) - 1) * q = (2 * (r : ℝ) - 1) * q + 2*q by ring]
      exact paymentPartition_addPart v R G hG hpay
        (ih (R \ G) hr' (fun g hg => hc g (Finset.mem_sdiff.mp hg).1) hleft)

/-- Actual goods in one column, normalized to unit total. -/
noncomputable def normalizedColumnWeight {m n : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    (cols : Fin m → Fin n) (g : Fin m) : ℝ :=
  v g / bundleValue v (R.filter (fun a => cols a = cols g))

private theorem column_normalization {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (cols : Fin m → Fin n) {q : ℝ} (hq : 0 < q)
    (hc : ∀ j, q ≤ bundleValue v (R.filter (fun g => cols g = j))) :
    (∀ j, bundleValue (normalizedColumnWeight v R cols) (R.filter (fun g => cols g = j)) = 1) ∧
    (∀ g ∈ R, normalizedColumnWeight v R cols g ≤ 1) ∧
    (∀ g, 0 ≤ normalizedColumnWeight v R cols g) ∧
    (∀ g, q * normalizedColumnWeight v R cols g ≤ v g) := by
  have hpos (j : Fin n) : 0 < bundleValue v (R.filter (fun g => cols g = j)) := hq.trans_le (hc j)
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    unfold bundleValue
    calc
      _ = ∑ g ∈ R.filter (fun g => cols g = j), v g /
          (∑ g ∈ R.filter (fun g => cols g = j), v g) := by
        refine Finset.sum_congr rfl (fun g hg => ?_)
        unfold normalizedColumnWeight bundleValue
        rw [(Finset.mem_filter.mp hg).2]
      _ = 1 := by
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt (hpos j))
  · intro g hg
    dsimp [normalizedColumnWeight]
    apply (div_le_one₀ (hpos (cols g))).mpr
    exact Finset.single_le_sum (fun i _ => hv i) (Finset.mem_filter.mpr ⟨hg,rfl⟩)
  · intro g
    exact div_nonneg (hv g) (hpos _).le
  · intro g
    dsimp [normalizedColumnWeight]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (hpos _)).mpr
      (by rw [mul_comm (v g)]; exact mul_le_mul_of_nonneg_right (hc _) (hv g))

/-- Relabel the retained rows as a partition on the remaining goods. -/
theorem retained_rows_partition {m n : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    (rows : Fin m → Fin n) (D : Finset (Fin n)) {r : ℕ}
    (hr : 0 < r) (hsize : (Finset.univ \ D).card = r) {q : ℝ}
    (hrows : ∀ i ∉ D, q ≤ bundleValue v (R.filter (fun g => rows g = i))) :
    HasPaymentPartition v (R.filter (fun g => rows g ∉ D)) r q := by
  classical
  let kept := Finset.univ \ D
  let e := Finset.equivFinOfCardEq hsize
  let f : Fin m → Fin r := fun g => if h : rows g ∈ kept then e ⟨rows g,h⟩ else ⟨0,hr⟩
  refine ⟨f,fun j => ?_⟩
  let i := (e.symm j).val
  have hi : i ∉ D := (Finset.mem_sdiff.mp (e.symm j).property).2
  have heq : (R.filter (fun g => rows g ∉ D)).filter (fun g => f g = j) =
      R.filter (fun g => rows g = i) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hg,hout⟩,hf⟩
      have hm : rows g ∈ kept := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hout⟩
      have h' : e ⟨rows g,hm⟩ = j := by simpa only [f,dif_pos hm] using hf
      exact ⟨hg, congrArg Subtype.val (e.injective (h'.trans (e.apply_symm_apply j).symm))⟩
    · rintro ⟨hg,hgi⟩
      have hout : rows g ∉ D := hgi ▸ hi
      have hm : rows g ∈ kept := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hout⟩
      refine ⟨⟨hg,hout⟩,?_⟩
      have hsub : (⟨rows g,hm⟩ : ↥kept) = e.symm j := Subtype.ext hgi
      simp [f,hm,hsub]
  rw [heq]
  exact hrows _ hi

/-- The general residual row estimate (n/(n+r-1)) in normalized weights. -/
theorem residual_normalized_rows {m n r : ℕ} (w : Fin m → ℝ)
    (R : Finset (Fin m)) (rows : Fin m → Fin n) (D : Finset (Fin n))
    (hr : 0 < r) (hsize : (Finset.univ \ D).card = r)
    (hcap : ∀ g ∈ R, w g ≤ 1)
    (htotal : bundleValue w R = n)
    (hsorted : ∀ i ∈ D, ∀ j ∉ D,
      bundleValue w (R.filter (fun g => rows g = i)) ≤ bundleValue w (R.filter (fun g => rows g = j))) :
    HasPaymentPartition w (R.filter (fun g => rows g ∉ D)) r
      ((n : ℝ) / ((n : ℝ) + r - 1)) := by
  let q := (n : ℝ) / ((n : ℝ) + r - 1)
  let U := R.filter (fun g => rows g ∉ D)
  change HasPaymentPartition w U r q
  by_cases hq : ∀ j ∉ D, q ≤ bundleValue w (R.filter (fun g => rows g = j))
  · exact retained_rows_partition w R rows D hr hsize hq
  push_neg at hq
  obtain ⟨j,hj,hsmall⟩ := hq
  have hcard := Finset.card_sdiff (Finset.subset_univ D)
  rw [Finset.card_univ,Fintype.card_fin,hsize] at hcard
  have hadd : D.card + r = n := by
    have h := Finset.card_le_univ D
    simp only [Fintype.card_fin] at h
    omega
  have hrn : r ≤ n := by omega
  have hn : 0 < n := by omega
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsubR : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hden : 0 < ((n : ℝ) + r - 1) := by linarith
  have hpos : 0 < q := div_pos hnR hden
  have hhalf : 1 ≤ 2*q := by
    dsimp [q]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hden).mpr (by linarith)
  have hloss : bundleValue w (R.filter (fun g => rows g ∈ D)) ≤ (D.card : ℝ) * q := by
    rw [← selected_parts_sum w R rows D]
    calc
      _ ≤ ∑ _i ∈ D, q := Finset.sum_le_sum (fun i hi => (hsorted i hi j hj).trans hsmall.le)
      _ = _ := by simp [nsmul_eq_mul]
  have hdiff : R \ R.filter (fun g => rows g ∈ D) = U := by
    ext g
    simp only [U,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have hsplit := bundleValue_sdiff w (Finset.filter_subset (fun g => rows g ∈ D) R)
  rw [hdiff,htotal] at hsplit
  have hmass : (2*(r : ℝ)-1)*q ≤ bundleValue w U := by
    have he : ((n : ℝ) + r - 1)*q = n := by
      exact mul_div_cancel₀ _ hden.ne'
    have hc : (D.card : ℝ) + r = n := by exact_mod_cast hadd
    linarith [show ((n : ℝ)+r-1)*q = (D.card : ℝ)*q+(2*(r : ℝ)-1)*q by rw [← hc]; ring]
  exact partition_from_bounded_mass w U hr hpos
    (fun g hg => (hcap g (Finset.mem_filter.mp hg).1).trans hhalf) hmass

/-- Move the weight threshold back to the original user's valuation. -/
theorem transfer_weight_partition {m r : ℕ} (v w : Fin m → ℝ) (U : Finset (Fin m))
    {q β : ℝ} (hq : 0 ≤ q) (hweight : ∀ g, q * w g ≤ v g)
    (h : HasPaymentPartition w U r β) :
    HasPaymentPartition v U r (q*β) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p,fun i => ?_⟩
  calc
    _ ≤ q * bundleValue w (U.filter (fun g => p g = i)) := mul_le_mul_of_nonneg_left (hp i) hq
    _ = ∑ g ∈ U.filter (fun g => p g = i), q*w g := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun g _ => hweight g)

theorem residual_rows_for_other_type {m n r : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin n) (D : Finset (Fin n))
    (hr : 0 < r) (hsize : (Finset.univ \ D).card = r)
    {q : ℝ} (hq : 0 ≤ q) (hcols : ∀ j, q ≤ bundleValue v (R.filter (fun g => cols g = j)))
    (hsorted : let w := normalizedColumnWeight v R cols
      ∀ i ∈ D, ∀ j ∉ D,
        bundleValue w (R.filter (fun g => rows g = i)) ≤ bundleValue w (R.filter (fun g => rows g = j))) :
    HasPaymentPartition v (R.filter (fun g => rows g ∉ D)) r
      (q * ((n : ℝ) / ((n : ℝ) + r - 1))) := by
  by_cases hz : q = 0
  · subst q
    let default : Fin r := ⟨0, hr⟩
    refine ⟨fun _ => default,fun j => ?_⟩
    rw [zero_mul]
    exact Finset.sum_nonneg (fun g _ => hv g)
  have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
  let w := normalizedColumnWeight v R cols
  obtain ⟨hunit,hcap,_,htransfer⟩ := column_normalization v hv R cols hp hcols
  have htotal : bundleValue w R = n := by
    rw [← sum_paymentParts w R cols]
    simp [w,hunit]
  exact transfer_weight_partition v w _ hq htransfer
    (residual_normalized_rows w R rows D hr hsize hcap htotal hsorted)

private theorem one_row_normalized_three_quarters {m r : ℕ} (w : Fin m → ℝ)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin (r+1)) (i : Fin (r+1))
    (hr : 2 ≤ r) (hw : ∀ g, 0 ≤ w g) (hcols : ∀ j, bundleValue w (R.filter (fun g => cols g = j)) = 1)
    (hsmallest : ∀ j, bundleValue w (R.filter (fun g => rows g = i)) ≤
      bundleValue w (R.filter (fun g => rows g = j))) :
    HasPaymentPartition w (R.filter (fun g => rows g ≠ i)) r (3/4) := by
  classical
  let U := R.filter (fun g => rows g ≠ i)
  by_cases hret : ∀ j ≠ i, (3 / 4 : ℝ) ≤ bundleValue w (R.filter (fun g => rows g = j))
  · have hsize : (Finset.univ \ ({i} : Finset (Fin (r + 1)))).card = r := by
      rw [Finset.card_sdiff (Finset.subset_univ _)]
      simp
    simpa using retained_rows_partition w R rows {i} (show 0 < r by omega) hsize
      (fun j hj => hret j (by simpa using hj))
  push_neg at hret
  obtain ⟨j,hj,hsmall⟩ := hret
  let D := R.filter (fun g => rows g = i)
  have hD : bundleValue w D < 3/4 := (hsmallest j).trans_lt hsmall
  let loss (j : Fin (r+1)) := bundleValue w (D.filter (fun g => cols g = j))
  have hf (j : Fin (r+1)) : 0 ≤ loss j := Finset.sum_nonneg (fun g _ => hw g)
  have hsum : (∑ j, loss j) = bundleValue w D := sum_paymentParts w D cols
  have hleft (j : Fin (r+1)) :
      bundleValue w (U.filter (fun g => cols g = j)) + loss j = 1 := by
    have hsub : D.filter (fun g => cols g = j) ⊆ R.filter (fun g => cols g = j) := by
      intro g hg
      simp only [D,Finset.mem_filter, and_assoc] at hg ⊢
      aesop
    have he : (R.filter (fun g => cols g = j)) \ (D.filter (fun g => cols g = j)) =
        U.filter (fun g => cols g = j) := by
      ext g
      simp only [D,U,Finset.mem_filter,Finset.mem_sdiff]
      tauto
    have e := bundleValue_sdiff w hsub
    simpa [he,hcols j] using e
  let H := Finset.univ.filter (fun j => (1/4 : ℝ) < loss j)
  have hH : H.card ≤ 2 := by
    by_contra! hc
    have hsize : (3 : ℝ) ≤ H.card := by exact_mod_cast (show 3 ≤ H.card by omega)
    have hlower : (H.card : ℝ) * (1/4 : ℝ) ≤ ∑ j ∈ H, loss j := by
      calc
        _ = ∑ _j ∈ H, (1/4 : ℝ) := by simp [nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2.le)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun j _ _ => hf j)
    rw [hsum] at hle
    linarith
  obtain ⟨H',hsub,_,hsize⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ H) hH
    (show 2 ≤ (Finset.univ : Finset (Fin (r+1))).card by simp; omega)
  obtain ⟨a,b,hab,hH'⟩ := Finset.card_eq_two.mp hsize
  have hall (j : Fin (r+1)) (ha : j ≠ a) (hb : j ≠ b) : loss j ≤ 1/4 := by
    by_contra! hbig
    have hh : (1/4 : ℝ) < loss j := hbig
    have hj : j ∈ H' := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    simp [hH',ha,hb] at hj
  have hpair : loss a + loss b ≤ bundleValue w D := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({a,b} : Finset (Fin (r+1))))
      (fun j _ _ => hf j)
    rw [hsum] at h
    simpa [hab] using h
  let merge (j : Fin (r+1)) := if j = b then a else j
  have hno (j : Fin (r+1)) : merge j ≠ b := by by_cases h : j=b <;> simp [merge,h,hab]
  let p : Fin m → Fin r := fun g => Classical.choose (Fin.exists_succAbove_eq (hno (cols g)))
  have hp (g : Fin m) : b.succAbove (p g) = merge (cols g) :=
    Classical.choose_spec (Fin.exists_succAbove_eq (hno (cols g)))
  refine ⟨p,fun c => ?_⟩
  let j := b.succAbove c
  have hjb : j ≠ b := Fin.succAbove_ne _ _
  let T := U.filter (fun g => p g = c)
  have hcolSub (i : Fin (r+1)) (hi : merge i = j) :
      U.filter (fun g => cols g = i) ⊆ T := by
    intro g hg
    obtain ⟨hU,hg⟩ := Finset.mem_filter.mp hg
    have heq : b.succAbove (p g) = b.succAbove c := by
      change b.succAbove (p g) = j
      rw [hp,hg,hi]
    exact Finset.mem_filter.mpr ⟨hU,Fin.succAbove_right_injective heq⟩
  change (3/4 : ℝ) ≤ bundleValue w T
  by_cases hja : j = a
  · have ha' : U.filter (fun g => cols g = a) ⊆ T :=
      hcolSub a (by simp [merge,hab,hja])
    have hb' : U.filter (fun g => cols g = b) ⊆ T :=
      hcolSub b (by simp [merge,hja])
    have hd : Disjoint (U.filter (fun g => cols g = a)) (U.filter (fun g => cols g = b)) := by
      apply Finset.disjoint_left.mpr
      intro g ha hb
      exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
    have hval := bundleValue_mono w hw (Finset.union_subset ha' hb')
    change (∑ g ∈ (U.filter (fun g => cols g = a)) ∪ (U.filter (fun g => cols g = b)), w g) ≤ _ at hval
    rw [Finset.sum_union hd] at hval
    change bundleValue w (U.filter (fun g => cols g = a)) +
      bundleValue w (U.filter (fun g => cols g = b)) ≤ _ at hval
    linarith [hleft a,hleft b]
  · have hsub : U.filter (fun g => cols g = j) ⊆ T :=
      hcolSub j (by simp [merge,hjb])
    linarith [bundleValue_mono w hw hsub,hleft j,hall j hja hjb]

theorem residual_one_row_three_quarters {m r : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin (r+1)) (i : Fin (r+1))
    (hr : 2 ≤ r) {q : ℝ} (hq : 0 ≤ q)
    (hcols : ∀ j, q ≤ bundleValue v (R.filter (fun g => cols g = j)))
    (hsmallest : let w := normalizedColumnWeight v R cols
      ∀ j, bundleValue w (R.filter (fun g => rows g = i)) ≤
        bundleValue w (R.filter (fun g => rows g = j))) :
    HasPaymentPartition v (R.filter (fun g => rows g ≠ i)) r (q*(3/4)) := by
  by_cases hz : q = 0
  · subst q
    let default : Fin r := ⟨0, show 0 < r by omega⟩
    refine ⟨fun _ => default,fun j => ?_⟩
    rw [zero_mul]
    exact Finset.sum_nonneg (fun g _ => hv g)
  have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
  obtain ⟨hunit,_,hnn,htransfer⟩ := column_normalization v hv R cols hp hcols
  exact transfer_weight_partition v _ _ hq htransfer
    (one_row_normalized_three_quarters _ R rows cols i hr hnn hunit hsmallest)

end OnlineMMS
