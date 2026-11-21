import OnlineMMS.FiniteRowBalance
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

private abbrev Cell := Fin 3 × Fin 3

private def rowCells (i : Fin 3) : List Cell := [(i,0),(i,1),(i,2)]
private def rowWeight (w : Cell → ℝ) (i : Fin 3) : ℝ := listWeight w (rowCells i)

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

private theorem triple_covers {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (x : Fin 3) : x = a ∨ x = b ∨ x = c := by
  have va := a.isLt
  have vb := b.isLt
  have vc := c.isLt
  have vx := x.isLt
  have vab : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have vac : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have vbc : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have heq : x.val = a.val ∨ x.val = b.val ∨ x.val = c.val := by omega
  exact heq.elim (fun h => Or.inl (Fin.ext h))
    (fun h => h.elim (fun h' => Or.inr (Or.inl (Fin.ext h'))) (fun h' => Or.inr (Or.inr (Fin.ext h'))))

private theorem third_label {a b : Fin 3} (h : a ≠ b) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  let c : Fin 3 := ⟨3 - a.val - b.val, by
    have ha := a.isLt
    have hb := b.isLt
    have hv : a.val ≠ b.val := fun hv => h (Fin.ext hv)
    omega⟩
  refine ⟨c, ?_, ?_⟩
  · intro he
    have hm := congrArg Fin.val he
    dsimp [c] at hm
    have ha := a.isLt
    have hb := b.isLt
    have hv : a.val ≠ b.val := fun hv => h (Fin.ext hv)
    omega
  · intro he
    have hm := congrArg Fin.val he
    dsimp [c] at hm
    have ha := a.isLt
    have hb := b.isLt
    have hv : a.val ≠ b.val := fun hv => h (Fin.ext hv)
    omega

private theorem triple_perm {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ([a,b,c] : List (Fin 3)).Perm [0,1,2] := by
  apply (List.perm_ext_iff_of_nodup (by simp [hab,hac,hbc]) (by decide)).mpr
  intro x
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨fun _ => fin3_cases x, fun _ => triple_covers hab hac hbc x⟩

private theorem sum_triple (f : Fin 3 → ℝ) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ j, f j) = f a + f b + f c := by
  have hp := ((triple_perm hab hac hbc).map f).sum_eq
  simp [Fin.sum_univ_three] at *
  linarith

private theorem rowWeight_eq (w : Cell → ℝ) (i : Fin 3) :
    rowWeight w i = ∑ j : Fin 3, w (i,j) := by
  simp [rowWeight, listWeight, rowCells, Fin.sum_univ_three]
  ring

private theorem sum_matrix_rows (w : Cell → ℝ) (hcol : ∀ j : Fin 3, (∑ i : Fin 3, w (i,j)) = 10) :
    (∑ i, rowWeight w i) = 30 := by
  simp_rw [rowWeight_eq]
  rw [Finset.sum_comm]
  norm_num [hcol]

private theorem rowCells_mem (i : Fin 3) (x : Cell) : x ∈ rowCells i ↔ x.1 = i := by
  obtain ⟨a,b⟩ := x
  simp only [rowCells, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  rcases fin3_cases b with h | h | h <;> simp [h]

private theorem rowCells_nodup (i : Fin 3) : (rowCells i).Nodup := by
  simp [rowCells]

private theorem pair_rows_perm {i j : Fin 3} (hij : i ≠ j) {L : List Cell}
    (hnd : L.Nodup) (hm : ∀ x : Cell, x ∈ L ↔ x.1 = i ∨ x.1 = j) :
    L.Perm (rowCells i ++ rowCells j) := by
  have hdisj : List.Disjoint (rowCells i) (rowCells j) := by
    intro x hx hy
    exact hij (((rowCells_mem i x).mp hx).symm.trans ((rowCells_mem j x).mp hy))
  apply (List.perm_ext_iff_of_nodup hnd ((rowCells_nodup i).append (rowCells_nodup j) hdisj)).mpr
  intro x
  simpa [rowCells_mem] using hm x

private def RowsCanSplit (w : Cell → ℝ) (i j : Fin 3) : Prop :=
  ∃ A B : List Cell, (A ++ B).Perm (rowCells i ++ rowCells j) ∧
      9 ≤ listWeight w A ∧ 9 ≤ listWeight w B

private theorem split_comm {w : Cell → ℝ} {i j : Fin 3}
    (h : RowsCanSplit w i j) : RowsCanSplit w j i := by
  obtain ⟨A,B,hperm,hA,hB⟩ := h
  exact ⟨A,B,hperm.trans List.perm_append_comm,hA,hB⟩

private theorem split_of_small_difference (w : Cell → ℝ) (i j : Fin 3) {A B : List Cell}
    (hperm : (A ++ B).Perm (rowCells i ++ rowCells j)) {D : ℝ}
    (htot : 18 + D ≤ rowWeight w i + rowWeight w j)
    (hD : |listWeight w A - listWeight w B| < D) : RowsCanSplit w i j := by
  have hw := (hperm.map w).sum_eq
  change listWeight w (A ++ B) = listWeight w (rowCells i ++ rowCells j) at hw
  simp only [listWeight_append] at hw
  have hsum : listWeight w A + listWeight w B = rowWeight w i + rowWeight w j := hw
  obtain ⟨hl, hr⟩ := abs_lt.mp hD
  exact ⟨A,B,hperm,by linarith,by linarith⟩

private theorem desc_fin3 (f : Fin 3 → ℝ) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f b ≤ f a ∧ f c ≤ f b := by
  rcases le_total (f 1) (f 0) with h10 | h01
  · rcases le_total (f 2) (f 1) with h21 | h12
    · exact ⟨0,1,2, by decide, by decide, by decide,h10,h21⟩
    · rcases le_total (f 2) (f 0) with h20 | h02
      · exact ⟨0,2,1, by decide, by decide, by decide,h20,h12⟩
      · exact ⟨2,0,1, by decide, by decide, by decide,h02,h10⟩
  · rcases le_total (f 2) (f 0) with h20 | h02
    · exact ⟨1,0,2, by decide, by decide, by decide,h01,h20⟩
    · rcases le_total (f 2) (f 1) with h21 | h12
      · exact ⟨1,2,0, by decide, by decide, by decide,h21,h02⟩
      · exact ⟨2,1,0, by decide, by decide, by decide,h12,h01⟩

private theorem light_cells_gt_one (w : Cell → ℝ)
    (hnonneg : ∀ x, 0 ≤ w x)
    (hcol : ∀ j : Fin 3, (∑ i : Fin 3, w (i,j)) = 10)
    {i j u : Fin 3} (hij : i ≠ j) (hiu : i ≠ u) (hju : j ≠ u)
    (hi : rowWeight w i < 9) (hnosplit : ¬RowsCanSplit w j u) :
    ∀ c : Fin 3, 1 < w (i,c) := by
  intro c
  by_contra! hc
  -- Use the two columns complementary to c.
  let a := c.succAbove (0 : Fin 2)
  let b := c.succAbove (1 : Fin 2)
  have hca : c ≠ a := (Fin.succAbove_ne _ _).symm
  have hcb : c ≠ b := (Fin.succAbove_ne _ _).symm
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 2) ≠ 1) (Fin.succAbove_right_injective h)
  let A : List Cell := [(j,c),(u,c)]
  let B : List Cell := [(j,a),(j,b),(u,a),(u,b)]
  have hp : (A ++ B).Perm (rowCells j ++ rowCells u) := by
    apply pair_rows_perm hju
    · simp [A,B,hju,hju.symm,hca,hcb,hab]
    · rintro ⟨r,s⟩
      have hc' := triple_covers hca hcb hab s
      simp only [A,B,List.cons_append,List.nil_append,List.mem_cons,Prod.mk.injEq,
        List.not_mem_nil,or_false]
      tauto
  have ht := sum_triple (rowWeight w) hij hiu hju
  rw [sum_matrix_rows w hcol] at ht
  have hsum := (hp.map w).sum_eq
  change listWeight w (A ++ B) = listWeight w (rowCells j ++ rowCells u) at hsum
  simp only [listWeight_append] at hsum
  change listWeight w A + listWeight w B = rowWeight w j + rowWeight w u at hsum
  have hcolumn := sum_triple (fun r => w (r,c)) hij hiu hju
  rw [hcol] at hcolumn
  have hA : listWeight w A = w (j,c) + w (u,c) := by simp [A,listWeight]
  exact hnosplit ⟨A,B,hp,by linarith,by linarith [hnonneg (i,c)]⟩

private theorem light_pair_large_cell (w : Cell → ℝ)
    (hnonneg : ∀ x, 0 ≤ w x)
    (hcol : ∀ j : Fin 3, (∑ i : Fin 3, w (i,j)) = 10)
    {i j u : Fin 3} (hij : i ≠ j) (hiu : i ≠ u) (hju : j ≠ u)
    (hi : rowWeight w i < 9) (hj : rowWeight w j < 9)
    (hj1 : ∀ c : Fin 3, 1 < w (j,c)) (hu8 : ∀ c : Fin 3, w (u,c) < 8)
    (hnosplit : ¬RowsCanSplit w j u) :
    (7 < rowWeight w i) ∧ (7 < rowWeight w j → ∃ c : Fin 3, 5 < w (j,c)) := by
  obtain ⟨a,b,c,hab,hac,hbc,habw,hbcw⟩ := desc_fin3 (fun c : Fin 3 => w (j,c))
  have hrow := sum_triple (fun c : Fin 3 => w (j,c)) hab hac hbc
  rw [← rowWeight_eq] at hrow
  have hjab : w (j,b) ≤ w (j,a) := habw
  have hjbc : w (j,c) ≤ w (j,b) := hbcw
  have ha : 1 < w (j,a) := hj1 a
  have hb : 1 < w (j,b) := hj1 b
  have hc : 1 < w (j,c) := hj1 c
  have hγa : w (j,a) < 7 := by linarith
  have hγb : w (j,b) < 4 := by linarith
  have hγc : w (j,c) < 3 := by linarith
  obtain ⟨A₀,B₀,hperm₀,hd₀⟩ := greedy_balancing_split w (rowCells u) [] []
  have hd₀' : |listWeight w A₀ - listWeight w B₀| < 8 := by
    rw [hd₀]
    simp only [listWeight,List.map_nil,List.sum_nil,sub_self,abs_zero]
    apply greedyDifference_lt_of_bounded (by norm_num) (by norm_num)
    intro q hq
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
    refine ⟨hnonneg x, ?_⟩
    obtain ⟨r,c⟩ := x
    have he : r = u := (rowCells_mem u (r,c)).mp hx
    subst r
    exact hu8 c
  let J : List Cell := [(j,a),(j,b),(j,c)]
  obtain ⟨A,B,hperm,hd⟩ := greedy_balancing_split w J A₀ B₀
  have hJ : J.Perm (rowCells j) := (triple_perm hab hac hbc).map (fun c => (j,c))
  have hfull : (A ++ B).Perm (rowCells j ++ rowCells u) := by
    apply hperm.trans
    have h0 : (A₀ ++ B₀).Perm (rowCells u) := by simpa using hperm₀
    exact (h0.append hJ).trans List.perm_append_comm
  have htot := sum_triple (rowWeight w) hij hiu hju
  rw [sum_matrix_rows w hcol] at htot
  have hbound5 : |listWeight w A - listWeight w B| < 5 := by
    rw [hd]
    simp only [J,List.map_cons,List.map_nil]
    exact greedyDifference_three_lt (abs_nonneg _) (by linarith) (by linarith)
      (by linarith) (by linarith)
  constructor
  · by_contra! hi7
    exact hnosplit (split_of_small_difference w j u hfull (by linarith only [htot, hi7]) hbound5)
  · intro hj7
    by_contra! hlarge
    have hbound3 : |listWeight w A - listWeight w B| < 3 := by
      rw [hd]
      simp only [J,List.map_cons,List.map_nil]
      exact greedyDifference_three_lt (abs_nonneg _) (by linarith) (by linarith [hlarge a])
        (by linarith) hγc
    exact hnosplit (split_of_small_difference w j u hfull (by linarith only [htot, hi]) hbound3)

private theorem normalized_matrix_split' (w : Cell → ℝ)
    (hnn : ∀ x, 0 ≤ w x)
    (hcol : ∀ j : Fin 3, (∑ i : Fin 3, w (i,j)) = 10) :
    ∃ i j : Fin 3, i ≠ j ∧ RowsCanSplit w i j := by
  by_contra! hfail
  have hlight : ∃ i j : Fin 3, i ≠ j ∧ rowWeight w i < 9 ∧ rowWeight w j < 9 := by
    have hh (i j : Fin 3) (hne : i ≠ j) (hi : 9 ≤ rowWeight w i) : rowWeight w j < 9 := by
      by_contra! hj
      exact hfail i j hne ⟨rowCells i,rowCells j,List.Perm.refl _,hi,hj⟩
    by_cases h0 : rowWeight w 0 < 9
    · by_cases h1 : rowWeight w 1 < 9
      · exact ⟨0,1,by decide,h0,h1⟩
      · exact ⟨0,2,by decide,h0,hh 1 2 (by decide) (le_of_not_gt h1)⟩
    · exact ⟨1,2,by decide,hh 0 1 (by decide) (le_of_not_gt h0),hh 0 2 (by decide) (le_of_not_gt h0)⟩
  obtain ⟨i,j,hij,hi,hj⟩ := hlight
  obtain ⟨u,hiu,hju⟩ := third_label hij
  have hi1 := light_cells_gt_one w hnn hcol hij hiu hju hi (hfail j u hju)
  have hj1 := light_cells_gt_one w hnn hcol hij.symm hju hiu hj (hfail i u hiu)
  have hu8 (c : Fin 3) : w (u,c) < 8 := by
    have h := sum_triple (fun i => w (i,c)) hij hiu hju
    rw [hcol] at h
    linarith [hi1 c,hj1 c]
  have hji := light_pair_large_cell w hnn hcol hij hiu hju hi hj hj1 hu8 (hfail j u hju)
  have hij' := light_pair_large_cell w hnn hcol hij.symm hju hiu hj hi hi1 hu8 (hfail i u hiu)
  obtain ⟨b,hb⟩ := hji.2 hij'.1
  obtain ⟨a,ha⟩ := hij'.2 hji.1
  have hab : a ≠ b := by
    intro he
    subst b
    have h := sum_triple (fun r => w (r,a)) hij hiu hju
    rw [hcol] at h
    linarith [hnn (u,a)]
  obtain ⟨c,hac,hbc⟩ := third_label hab
  have hri := sum_triple (fun c => w (i,c)) hab hac hbc
  have hrj := sum_triple (fun c => w (j,c)) hab hac hbc
  rw [← rowWeight_eq] at hri hrj
  have hA : w (i,a) < 7 := by linarith [hi1 b,hi1 c]
  have hB : w (j,b) < 7 := by linarith [hj1 a,hj1 c]
  have hic : w (i,c) < 3 := by linarith [hi1 b]
  have hjc : w (j,c) < 3 := by linarith [hj1 a]
  have hja : w (j,a) < 3 := by linarith [hj1 c]
  have huca : w (u,a) < 4 := by
    have h := sum_triple (fun r => w (r,a)) hij hiu hju
    rw [hcol] at h
    linarith [hj1 a]
  have hucb : w (u,b) < 4 := by
    have h := sum_triple (fun r => w (r,b)) hij hiu hju
    rw [hcol] at h
    linarith [hi1 b]
  have hucc : 4 < w (u,c) := by
    have h := sum_triple (fun r => w (r,c)) hij hiu hju
    rw [hcol] at h
    linarith
  let X : List Cell := [(j,b)]
  let Y : List Cell := [(u,c)]
  let U : List Cell := [(u,a),(u,b)]
  let J : List Cell := [(j,a),(j,c)]
  obtain ⟨A₀,B₀,hp₀,hd₀⟩ := greedy_balancing_split w U X Y
  have hd₀' : |listWeight w A₀ - listWeight w B₀| < 4 := by
    rw [hd₀]
    refine greedyDifference_lt_of_bounded (abs_nonneg _) ?_ _ ?_
    · apply abs_lt.mpr
      simp only [X,Y,listWeight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      constructor <;> linarith [hu8 c]
    · intro q hq
      simp only [U,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨hnn _,huca⟩
      · exact ⟨hnn _,hucb⟩
  obtain ⟨A,B,hp,hd⟩ := greedy_balancing_split w J A₀ B₀
  have hperm : (A ++ B).Perm (rowCells j ++ rowCells u) := by
    apply hp.trans ((hp₀.append_right J).trans ?_)
    apply pair_rows_perm hju
    · simp [X,Y,U,J,hju,hju.symm,hab,hab.symm,hac,hac.symm,hbc,hbc.symm]
    · rintro ⟨r,s⟩
      have hcover := triple_covers hab hac hbc s
      simp only [X,Y,U,J,List.cons_append,List.nil_append,List.mem_cons,Prod.mk.injEq,
        List.not_mem_nil,or_false]
      tauto
  have hdiff : |listWeight w A - listWeight w B| < 3 := by
    rw [hd]
    simp only [J,List.map_cons,List.map_nil]
    exact greedyDifference_two_lt (abs_nonneg _) (by linarith [hj1 a,hj1 c])
      (by linarith [hj1 c]) hjc
  have ht := sum_triple (rowWeight w) hij hiu hju
  rw [sum_matrix_rows w hcol] at ht
  exact hfail j u hju (split_of_small_difference w j u hperm (by linarith only [ht,hi]) hdiff)

/-- The arithmetic core of the three-row lemma. The cells of two rows can
be divided into two bundles of normalized weight at least nine. -/
theorem normalized_matrix_split (w : Fin 3 × Fin 3 → ℝ)
    (hnn : ∀ x, 0 ≤ w x)
    (hcol : ∀ j : Fin 3, (∑ i : Fin 3, w (i,j)) = 10) :
    ∃ i j : Fin 3, i ≠ j ∧ ∃ A B : List (Fin 3 × Fin 3),
      (A ++ B).Perm ([(i,0),(i,1),(i,2),(j,0),(j,1),(j,2)] : List (Fin 3 × Fin 3)) ∧
      9 ≤ listWeight w A ∧ 9 ≤ listWeight w B := by
  obtain ⟨i,j,hij,A,B,hp,hA,hB⟩ := normalized_matrix_split' w hnn hcol
  exact ⟨i,j,hij,A,B,hp,hA,hB⟩

private theorem cellWeight_sum {m : ℕ} (tag : Fin m → Cell) (v : Fin m → ℝ)
    (R : Finset (Fin m)) {L : List Cell} (hn : L.Nodup) :
    listWeight (fun c => bundleValue v (R.filter (fun g => tag g = c))) L =
      bundleValue v (R.filter (fun g => tag g ∈ L)) := by
  induction L with
  | nil => simp [listWeight,bundleValue]
  | cons c L ih =>
    obtain ⟨hmem, hnd⟩ := List.nodup_cons.mp hn
    have hunion : (R.filter fun g => tag g ∈ c :: L) =
        (R.filter fun g => tag g = c) ∪ (R.filter fun g => tag g ∈ L) := by
      ext g
      simp only [Finset.mem_filter,Finset.mem_union,List.mem_cons]
      tauto
    have hd : Disjoint (R.filter fun g => tag g = c) (R.filter fun g => tag g ∈ L) := by
      apply Finset.disjoint_left.mpr
      intro g hg hg'
      exact hmem ((Finset.mem_filter.mp hg).2 ▸ (Finset.mem_filter.mp hg').2)
    rw [hunion, show bundleValue v
      ((R.filter fun g => tag g = c) ∪ (R.filter fun g => tag g ∈ L)) =
        bundleValue v (R.filter fun g => tag g = c) +
        bundleValue v (R.filter fun g => tag g ∈ L) from Finset.sum_union hd]
    change _ + listWeight _ L = _
    rw [ih hnd]

/-- The row-deletion lemma with actual goods as input. The two residual
bundles are unions of whole cells whenever the target is positive. -/
theorem choosing_row_preserves_nine_tenths {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows : Fin m → Fin 3) {q : ℝ}
    (hpartition : HasPaymentPartition v R 3 q) :
    ∃ deleted : Fin 3,
      HasPaymentPartition v (R \ R.filter (fun g => rows g = deleted)) 2 (9 / 10 * q) := by
  classical
  by_cases hq : 0 < q
  · obtain ⟨cols,hcols⟩ := hpartition
    let column (j : Fin 3) := R.filter (fun g => cols g = j)
    let weight : Fin m → ℝ := fun g => 10 * v g / bundleValue v (column (cols g))
    have hvcol (j : Fin 3) : 0 < bundleValue v (column j) := hq.trans_le (hcols j)
    have hwnn (g : Fin m) : 0 ≤ weight g := by
      exact div_nonneg (mul_nonneg (by norm_num) (hv g)) (hvcol (cols g)).le
    have hcolweight (j : Fin 3) : bundleValue weight (column j) = 10 := by
      unfold bundleValue
      calc
        _ = ∑ g ∈ column j, (10 / bundleValue v (column j)) * v g := by
          refine Finset.sum_congr rfl (fun g hg => ?_)
          have he := (Finset.mem_filter.mp hg).2
          dsimp [weight]
          rw [he, div_mul_eq_mul_div]
        _ = 10 := by
          rw [← Finset.mul_sum]
          change 10 / bundleValue v (column j) * bundleValue v (column j) = 10
          exact div_mul_cancel₀ _ (ne_of_gt (hvcol j))
    let tag : Fin m → Cell := fun g => (rows g, cols g)
    let w : Cell → ℝ := fun c => bundleValue weight (R.filter (fun g => tag g = c))
    have hwm : ∀ c, 0 ≤ w c := fun c => Finset.sum_nonneg (fun g _ => hwnn g)
    have hwcol (j : Fin 3) : (∑ i : Fin 3, w (i,j)) = 10 := by
      have hcells (i : Fin 3) : R.filter (fun g => tag g = (i,j)) =
          (column j).filter (fun g => rows g = i) := by
        ext g
        simp only [Finset.mem_filter,tag,column,Prod.mk.injEq]
        tauto
      have hs := sum_paymentParts weight (column j) rows
      simp only [w,hcells]
      exact hs.trans (hcolweight j)
    obtain ⟨a,b,hab,A,B,hperm,hwa,hwb⟩ := normalized_matrix_split w hwm hwcol
    obtain ⟨i,hai,hbi⟩ := third_label hab
    have hABnd : (A ++ B).Nodup := hperm.nodup_iff.mpr (by
      simp [hab,hab.symm])
    obtain ⟨hAn,hBn,hABdisj⟩ := List.nodup_append.mp hABnd
    let U := R \ R.filter (fun g => rows g = i)
    let GA := R.filter (fun g => tag g ∈ A)
    let GB := R.filter (fun g => tag g ∈ B)
    have hcover (g : Fin m) : tag g ∈ A ∨ tag g ∈ B ↔ rows g ≠ i := by
      have h := hperm.mem_iff (a := tag g)
      change tag g ∈ A ++ B ↔ tag g ∈ rowCells a ++ rowCells b at h
      simp only [List.mem_append,rowCells_mem,tag,Prod.fst] at h
      exact h.trans (by
        constructor
        · rintro (e | e)
          · exact e ▸ hai
          · exact e ▸ hbi
        · intro hne
          rcases triple_covers hab hai hbi (rows g) with e | e | e
          · exact Or.inl e
          · exact Or.inr e
          · exact (hne e).elim)
    have hGsub : GA ⊆ U := by
      intro g hg
      obtain ⟨hg,hA⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_sdiff.mpr ⟨hg,fun hin => (hcover g).mp (Or.inl hA) (Finset.mem_filter.mp hin).2⟩
    have hGcompl : U \ GA = GB := by
      ext g
      simp only [U,GA,GB,Finset.mem_sdiff,Finset.mem_filter]
      have hz := hcover g
      have hn : ¬ (tag g ∈ A ∧ tag g ∈ B) := fun h => hABdisj h.1 h.2
      tauto
    have hWA : 9 ≤ bundleValue weight GA := (cellWeight_sum tag weight R hAn) ▸ hwa
    have hWB : 9 ≤ bundleValue weight GB := (cellWeight_sum tag weight R hBn) ▸ hwb
    have htransfer (T : Finset (Fin m)) (hT : 9 ≤ bundleValue weight T) :
        (9 / 10) * q ≤ bundleValue v T := by
      have hpoint (g : Fin m) : q / 10 * weight g ≤ v g := by
        dsimp [weight]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (hvcol (cols g))).mpr
        calc
          _ = q * v g := by ring
          _ ≤ _ := by
            rw [mul_comm (v g)]
            exact mul_le_mul_of_nonneg_right (hcols (cols g)) (hv g)
      calc
        _ = q / 10 * 9 := by ring
        _ ≤ q / 10 * bundleValue weight T := mul_le_mul_of_nonneg_left hT (by positivity)
        _ = ∑ g ∈ T, q / 10 * weight g := Finset.mul_sum _ _ _
        _ ≤ _ := Finset.sum_le_sum (fun g _ => hpoint g)
    refine ⟨i,paymentPartition_two_of_cut hGsub (htransfer _ hWA) ?_⟩
    rw [hGcompl]
    exact htransfer _ hWB
  · refine ⟨0, fun g => 0, fun j => ?_⟩
    apply (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 9 / 10) (le_of_not_gt hq)).trans
    exact Finset.sum_nonneg (fun g _ => hv g)

end OnlineMMS
