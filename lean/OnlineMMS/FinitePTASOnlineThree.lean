import OnlineMMS.FinitePTASOnlineTwo
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Equiv.Fin.Basic

namespace OnlineMMS

open scoped BigOperators

private def cellRow (c : Fin 9) : Fin 3 := ((finProdFinEquiv (m := 3) (n := 3)).symm c).1
private def cellCol (c : Fin 9) : Fin 3 := ((finProdFinEquiv (m := 3) (n := 3)).symm c).2

private def cellTag {m : ℕ} (rows cols : Fin m → Fin 3) (g : Fin m) : Fin 9 :=
  finProdFinEquiv (rows g,cols g)

@[simp] private theorem cellRow_tag {m : ℕ} (rows cols : Fin m → Fin 3) (g : Fin m) :
    cellRow (cellTag rows cols g) = rows g := by simp [cellRow,cellTag]

@[simp] private theorem cellCol_tag {m : ℕ} (rows cols : Fin m → Fin 3) (g : Fin m) :
    cellCol (cellTag rows cols g) = cols g := by simp [cellCol,cellTag]

private def cellsIn {m : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin 9)
    (C : Finset (Fin 9)) : Finset (Fin m) :=
  R.filter (fun g => tag g ∈ C)

private theorem bundleValue_cellsIn {m : ℕ} (R : Finset (Fin m))
    (tag : Fin m → Fin 9) (C : Finset (Fin 9)) (v : Fin m → ℝ) :
    bundleValue (fun c => bundleValue v (R.filter (fun g => tag g = c))) C =
      bundleValue v (cellsIn R tag C) := by
  exact Finset.sum_fiberwise_eq_sum_filter R C tag v

private theorem cellsIn_diff {m : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin 9)
    (A B : Finset (Fin 9)) : cellsIn R tag (A \ B) = cellsIn R tag A \ cellsIn R tag B := by
  ext g
  simp only [cellsIn,Finset.mem_filter,Finset.mem_sdiff]
  tauto

private def retainedCells (i : Fin 3) : Finset (Fin 9) :=
  Finset.univ \ rationalPart Finset.univ cellRow i

private theorem cellsIn_retained {m : ℕ} (R : Finset (Fin m))
    (rows cols : Fin m → Fin 3) (i : Fin 3) :
    cellsIn R (cellTag rows cols) (retainedCells i) = R \ rationalPart R rows i := by
  ext g
  simp only [cellsIn,retainedCells,rationalPart,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,
    cellRow_tag,true_and]
  tauto

private def retainedCellList (i : Fin 3) : List (Fin 9) :=
  (List.finRange 9).filter (fun c => decide (cellRow c ≠ i))

private theorem retainedCellList_length (i : Fin 3) : (retainedCellList i).length = 6 := by
  fin_cases i <;> decide

private theorem mem_retainedCellList (i : Fin 3) (c : Fin 9) :
    c ∈ retainedCellList i ↔ c ∈ retainedCells i := by
  simp [retainedCellList,retainedCells,rationalPart,List.mem_finRange]

/-- Each of the three row deletions has six retained row-column cells. -/
def rationalThreeCandidates : List (Fin 3 × Finset (Fin 9)) :=
  (List.finRange 3).flatMap fun j =>
    (retainedCellList j).sublists.map fun cs => (j,cs.toFinset)

theorem rationalThreeCandidates_length : rationalThreeCandidates.length = 3 * 2^6 := by
  simp [rationalThreeCandidates,List.length_sublists,retainedCellList_length]

private theorem rationalThreeCandidates_mem (j : Fin 3) (K : Finset (Fin 9))
    (hK : K ⊆ retainedCells j) : (j,K) ∈ rationalThreeCandidates := by
  let L := (retainedCellList j).filter (fun c => decide (c ∈ K))
  have hL : L.toFinset = K := by
    ext c
    simp only [L,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,mem_retainedCellList]
    exact ⟨And.right,fun hc => ⟨hK hc,hc⟩⟩
  exact List.mem_flatMap.mpr ⟨j,List.mem_finRange _,
    List.mem_map.mpr ⟨L,List.mem_sublists.mpr List.filter_sublist,by rw [hL]⟩⟩

private def threeCut {m : ℕ} (R : Finset (Fin m)) (rows cols : Fin m → Fin 3)
    (key : Fin 3 × Finset (Fin 9)) : Finset (Fin m) :=
  cellsIn (R \ rationalPart R rows key.1) (cellTag rows cols) key.2

private def threeCutTest {m : ℕ} (v : Fin m → ℚ) (R : Finset (Fin m))
    (rows cols : Fin m → Fin 3) (q : ℚ) (key : Fin 3 × Finset (Fin 9)) : Bool :=
  let U := R \ rationalPart R rows key.1
  let G := threeCut R rows cols key
  decide ((9/10) * q ≤ rationalBundleValue v G ∧
    (9/10) * q ≤ rationalBundleValue v (U \ G))

private theorem threeCutTest_exists {m : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin 3) (q : ℚ)
    (h : rationalPartsPay v R cols q) :
    ∃ key ∈ rationalThreeCandidates, threeCutTest v R rows cols q key = true := by
  let vr : Fin m → ℝ := fun g => v g
  let tag := cellTag rows cols
  let w (c : Fin 9) := bundleValue vr (R.filter (fun g => tag g = c))
  have hvr (g : Fin m) : 0 ≤ vr g := by
    dsimp [vr]
    exact_mod_cast hv g
  have hw (c : Fin 9) : 0 ≤ w c := Finset.sum_nonneg (fun g _ => hvr g)
  have hp : HasPaymentPartition w Finset.univ 3 (q : ℝ) := by
    refine ⟨cellCol,fun j => ?_⟩
    change (q : ℝ) ≤ bundleValue w (rationalPart Finset.univ cellCol j)
    rw [bundleValue_cellsIn]
    have he : cellsIn R tag (rationalPart Finset.univ cellCol j) = rationalPart R cols j := by
      ext g
      simp [cellsIn,rationalPart,tag]
    rw [he,← rationalBundleValue_cast]
    exact_mod_cast h j
  obtain ⟨i,hi⟩ := choosing_row_preserves_nine_tenths w hw Finset.univ cellRow hp
  change HasPaymentPartition w (retainedCells i) 2 ((9/10)*(q : ℝ)) at hi
  obtain ⟨K,hK,h1,h2⟩ := paymentPartition_two_cut hi
  refine ⟨(i,K),rationalThreeCandidates_mem i K hK,?_⟩
  have hU : cellsIn R tag (retainedCells i) = R \ rationalPart R rows i :=
    cellsIn_retained R rows cols i
  have hcut : threeCut R rows cols (i,K) = cellsIn R tag K := by
    unfold threeCut
    simp only [← hU, cellsIn, Finset.filter_filter]
    ext g
    simp only [Finset.mem_filter]
    have hmem : tag g ∈ K → tag g ∈ retainedCells i := fun hk => hK hk
    tauto
  rw [bundleValue_cellsIn] at h1 h2
  rw [cellsIn_diff,hU] at h2
  simp only [threeCutTest,decide_eq_true_eq, hcut]
  constructor
  · rw [← rationalBundleValue_cast] at h1
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact h1
  · rw [← rationalBundleValue_cast] at h2
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact h2

private def chooseRationalThreeCut {m : ℕ} (v : Fin m → ℚ) (R : Finset (Fin m))
    (rows cols : Fin m → Fin 3) (q : ℚ) : Fin 3 × Finset (Fin 9) :=
  (rationalThreeCandidates.find? (threeCutTest v R rows cols q)).getD (0,∅)

private theorem chooseRationalThreeCut_passes {m : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin 3) (q : ℚ)
    (h : rationalPartsPay v R cols q) :
    threeCutTest v R rows cols q (chooseRationalThreeCut v R rows cols q) = true := by
  obtain ⟨key,hkey,hpass⟩ := threeCutTest_exists v hv R rows cols q h
  unfold chooseRationalThreeCut
  cases he : rationalThreeCandidates.find? (threeCutTest v R rows cols q) with
  | none => exact ((List.find?_eq_none.mp he) key hkey hpass).elim
  | some k => exact List.find?_some he

private theorem retainedRow_cut {m : ℕ} (v : Fin m → ℚ) (R : Finset (Fin m))
    (rows : Fin m → Fin 3) (q : ℚ) (h : rationalPartsPay v R rows q) (j : Fin 3) :
    rationalCutPays v (R \ rationalPart R rows j)
      (rationalPart R rows (j.succAbove 0)) q := by
  let A := rationalPart R rows j
  let G := rationalPart R rows (j.succAbove 0)
  have hG : G ⊆ R \ A := by
    intro g hg
    obtain ⟨hg,he⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_sdiff.mpr ⟨hg,fun ha => (j.succAbove_ne 0)
      (he.symm.trans (Finset.mem_filter.mp ha).2)⟩
  have hc : (R \ A) \ G = rationalPart R rows (j.succAbove 1) := by
    ext g
    have hlabels : rows g = j ∨ rows g = j.succAbove 0 ∨ rows g = j.succAbove 1 := by
      by_cases hj : rows g = j
      · exact Or.inl hj
      · obtain ⟨z,hz⟩ := Fin.exists_succAbove_eq hj
        rcases shortType_cases 0 z with h0 | h1
        · exact Or.inr (Or.inl (h0 ▸ hz.symm))
        · have h1' : z = 1 := h1
          exact Or.inr (Or.inr (h1' ▸ hz.symm))
    rcases hlabels with h' | h' | h'
    · simp [A,G,rationalPart,h',Ne.symm (j.succAbove_ne 1)]
    · simp [A,G,rationalPart,h',Fin.succAbove_right_inj]
    · simp [A,G,rationalPart,h',Fin.succAbove_right_inj,j.succAbove_ne]
  exact ⟨hG,h _,by rw [hc]; exact h _⟩

/-- Apply the three-arrival rule after seeing the first type. Its pair
contains the first allocation and the executable two-arrival continuation. -/
def rationalThreeChoice {m : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (parts : Fin 2 → Fin m → Fin 3) (q : Fin 2 → ℚ) (first : Fin 2) :
    Finset (Fin m) × Policy m 2 2 :=
  let other := otherShortType first
  let rows := parts first
  let cols := parts other
  let key := chooseRationalThreeCut (v other) R rows cols (q other)
  let G := rationalPart R rows key.1
  let cuts := fun t => if t = first then rationalPart R rows (key.1.succAbove 0)
    else threeCut R rows cols key
  (G, rationalTwoPolicy v (R \ G) cuts)

theorem rationalThreeChoice_correct {m : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m))
    (parts : Fin 2 → Fin m → Fin 3) (q : Fin 2 → ℚ)
    (h : ∀ t, rationalPartsPay (v t) R (parts t) (q t)) (first : Fin 2) :
    let ans := rationalThreeChoice v R parts q first
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    ans.1 ⊆ R ∧ (q first : ℝ) ≤ bundleValue (w first) ans.1 ∧
      ans.2.Guarantees w (orientedTarget (fun t => (q t : ℝ)) 1 (9/10) first) (R \ ans.1) := by
  let other := otherShortType first
  let rows := parts first
  let cols := parts other
  let key := chooseRationalThreeCut (v other) R rows cols (q other)
  let G := rationalPart R rows key.1
  let cuts := fun t => if t = first then rationalPart R rows (key.1.succAbove 0)
    else threeCut R rows cols key
  have htest := chooseRationalThreeCut_passes (v other) (hv other) R rows cols (q other) (h other)
  change threeCutTest (v other) R rows cols (q other) key = true at htest
  simp only [threeCutTest,decide_eq_true_eq] at htest
  have hparts : ∀ t, rationalCutPays (v t) (R \ G) (cuts t)
      ((if t = first then 1 else (9/10)) * q t) := by
    intro t
    rcases shortType_cases first t with ht | ht
    · rw [ht]
      simpa [cuts] using retainedRow_cut (v first) R rows (q first) (h first) key.1
    · rw [ht]
      have hn : otherShortType first ≠ first := otherShortType_ne first
      simp only [cuts,if_neg hn]
      exact ⟨Finset.filter_subset _ _,htest.1,htest.2⟩
  change G ⊆ R ∧ (q first : ℝ) ≤ bundleValue (fun g => (v first g : ℝ)) G ∧ _
  refine ⟨rationalPart_subset _ _ _,?_,?_⟩
  · rw [← rationalBundleValue_cast]
    exact_mod_cast h first key.1
  · have hp := rationalTwoPolicy_correct v (R \ G) _ cuts hparts
    apply hp.mono
    intro t
    by_cases he : t = first <;> norm_num [orientedTarget,he,Rat.cast_mul,Rat.cast_div]

/-- Compute the first allocation and continuation with the PTAS partitions. -/
def rationalThreePTASChoice {m L : ℕ} (v : Fin 2 → Fin m → ℚ) (first : Fin 2) :
    Finset (Fin m) × Policy m 2 2 :=
  rationalThreeChoice v Finset.univ
    (fun t => rationalMMSAssignment (L := L) (v t) (by decide : 0 < 3))
    (fun t => rationalMMSPayment (L := L) (v t) (by decide : 0 < 3)) first

theorem rationalThreePTASChoice_correct {m L : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hL : 0 < L) (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) 3 (by decide)
    let ans := rationalThreePTASChoice (L := L) v first
    (1-(1 : ℝ)/L)*μ first ≤ bundleValue (w first) ans.1 ∧
    ans.2.Guarantees w (fun t => (1-(1 : ℝ)/L)*orientedTarget μ 1 (9/10) first t)
      (Finset.univ \ ans.1) := by
  dsimp only
  unfold rationalThreePTASChoice
  obtain ⟨_,hfirst,hrest⟩ := rationalThreeChoice_correct v hv Finset.univ _ _
    (fun t => rationalPartsPay_ptas (L := L) (v t) (by decide : 0 < 3)) first
  have ha (t : Fin 2) : (1-(1 : ℝ)/L)*maximinShare (fun g => (v t g : ℝ)) 3 (by decide) ≤
      (rationalMMSPayment (L := L) (v t) (by decide : 0 < 3) : ℝ) := by
    rw [rationalMMSPayment_cast]
    apply Finset.le_inf'
    intro i _
    exact rationalMMSAssignment_guarantee (v t) (hv t) (by decide) hL i
  exact ⟨(ha first).trans hfirst,oriented_approximate_partition_transfer first
    (by norm_num) (by norm_num) ha hrest⟩

/-- The work model counts per-good membership checks and per-good rational
additions in the two sums for each tested cell cut. -/
def rationalThreeCutScanWork (m : ℕ) : ℕ :=
  rationalThreeCandidates.length * (8*m+3)

theorem rationalThreeCutScanWork_le (m : ℕ) :
    rationalThreeCutScanWork m ≤ 1536 * (m+1) := by
  simp only [rationalThreeCutScanWork,rationalThreeCandidates_length]
  omega

end OnlineMMS
