import OnlineMMS.FinitePartitions
import OnlineMMS.Uniform

namespace OnlineMMS

private def rowA : Fin 8 → ℕ := ![7, 1, 1, 3, 3, 3, 4, 5]
private def rowB : Fin 8 → ℕ := ![7, 1, 1, 3, 3, 3, 6, 6]
private def naturalValue (v : Fin 8 → ℕ) (G : Finset (Fin 8)) : ℕ := ∑ g ∈ G, v g

private def realValuation (t : Fin 2) (g : Fin 8) : ℝ :=
  if t = 0 then (rowA g : ℝ) else (rowB g : ℝ)

private theorem cast_naturalValue (v : Fin 8 → ℕ) (G : Finset (Fin 8)) :
    (naturalValue v G : ℝ) = bundleValue (fun g => (v g : ℝ)) G := by
  exact Nat.cast_sum _ _

private theorem valueA (G : Finset (Fin 8)) :
    bundleValue (realValuation 0) G = (naturalValue rowA G : ℝ) := by
  change bundleValue (fun g => (rowA g : ℝ)) G = _
  exact (cast_naturalValue _ _).symm

private theorem valueB (G : Finset (Fin 8)) :
    bundleValue (realValuation 1) G = (naturalValue rowB G : ℝ) := by
  change bundleValue (fun g => (rowB g : ℝ)) G = _
  exact (cast_naturalValue _ _).symm

private def partitionA : Fin 8 → Fin 3 := ![0,0,0,1,1,1,2,2]
private def partitionB : Fin 8 → Fin 3 := ![0,1,2,0,1,2,1,2]

private theorem witness_mms_A : maximinShare (realValuation 0) 3 (by decide) = 9 := by
  apply le_antisymm
  · apply (maximinShare_le_average _ (by decide)).trans
    have hv : naturalValue rowA Finset.univ = 27 := by decide
    rw [valueA,hv]
    norm_num
  · have hrows : ∀ j : Fin 3,
      naturalValue rowA (Finset.univ.filter fun g => partitionA g = j) = 9 := by decide
    apply le_trans _ (partitionMin_le_maximinShare (realValuation 0) (by decide) partitionA)
    apply Finset.le_inf'
    intro j _
    change (9 : ℝ) ≤ bundleValue (realValuation 0) (Finset.univ.filter fun g => partitionA g = j)
    rw [valueA,hrows]
    norm_num

private theorem witness_mms_B : maximinShare (realValuation 1) 3 (by decide) = 10 := by
  apply le_antisymm
  · apply (maximinShare_le_average _ (by decide)).trans
    have hv : naturalValue rowB Finset.univ = 30 := by decide
    rw [valueB,hv]
    norm_num
  · have hrows : ∀ j : Fin 3,
      naturalValue rowB (Finset.univ.filter fun g => partitionB g = j) = 10 := by decide
    apply le_trans _ (partitionMin_le_maximinShare (realValuation 1) (by decide) partitionB)
    apply Finset.le_inf'
    intro j _
    change (10 : ℝ) ≤ bundleValue (realValuation 1) (Finset.univ.filter fun g => partitionB g = j)
    rw [valueB,hrows]
    norm_num

private def paysTwo (v : Fin 8 → ℕ) (q : ℕ) (R : Finset (Fin 8)) : Prop :=
  ∃ G ∈ R.powerset, q ≤ naturalValue v G ∧ q ≤ naturalValue v (R \ G)

private instance (v : Fin 8 → ℕ) (q : ℕ) (R : Finset (Fin 8)) : Decidable (paysTwo v q R) := by
  unfold paysTwo
  infer_instance

private def blockI : Finset (Fin 8) := {0,1,2}
private def blockJ : Finset (Fin 8) := {3,4,5}
private def blockK : Finset (Fin 8) := {6,7}
private def groups : Finset (Finset (Fin 8)) := {blockI,blockJ,blockK}

private theorem contain_seven (G : Finset (Fin 8)) (hG : naturalValue rowA G = 9)
    (h0 : 0 ∈ G) : G = blockI := by
  let tail := G.erase 0
  have he : naturalValue rowA tail = 2 := by
    have hs := Finset.sum_erase_add G rowA h0
    change naturalValue rowA tail + rowA 0 = naturalValue rowA G at hs
    have hprice : rowA 0 = 7 := by decide
    rw [hG,hprice] at hs
    omega
  have hprice : ∀ g : Fin 8, g ≠ 0 → g ≠ 1 → g ≠ 2 → 3 ≤ rowA g := by decide
  have ht : tail ⊆ {1,2} := by
    intro g hg
    have hn : g ≠ 0 := (Finset.mem_erase.mp hg).1
    by_cases hg1 : g = 1
    · simp [hg1]
    by_cases hg2 : g = 2
    · simp [hg2]
    exfalso
    have hle : rowA g ≤ naturalValue rowA tail :=
      Finset.single_le_sum (fun g _ => Nat.zero_le (rowA g)) hg
    have hlarge := hprice g hn hg1 hg2
    omega
  have hc : naturalValue rowA tail = tail.card := by
    unfold naturalValue
    calc
      _ = ∑ _g ∈ tail, 1 := by
        refine Finset.sum_congr rfl fun g hg => ?_
        have hm := ht hg
        have hv : ∀ g : Fin 8, g ∈ ({1,2} : Finset (Fin 8)) → rowA g = 1 := by decide
        exact hv g hm
      _ = _ := by simp
  have ht' : tail = {1,2} := by
    apply Finset.eq_of_subset_of_card_le ht
    have h2 : ({1,2} : Finset (Fin 8)).card = 2 := by decide
    rw [← hc,he,h2]
  rw [← Finset.insert_erase h0]
  change insert (0 : Fin 8) tail = blockI
  rw [ht']
  rfl

private theorem contain_five (G : Finset (Fin 8)) (hG : naturalValue rowA G = 9)
    (h7 : 7 ∈ G) (hdisj : Disjoint G blockI) : G = blockK := by
  let tail := G.erase 7
  have he : naturalValue rowA tail = 4 := by
    have hs := Finset.sum_erase_add G rowA h7
    change naturalValue rowA tail + rowA 7 = naturalValue rowA G at hs
    have hprice : rowA 7 = 5 := by decide
    rw [hG,hprice] at hs
    omega
  have hkeep : 6 ∈ tail := by
    apply Classical.byContradiction
    intro h6
    have hc : naturalValue rowA tail = tail.card * 3 := by
      unfold naturalValue
      calc
        _ = ∑ _g ∈ tail, 3 := by
          refine Finset.sum_congr rfl fun g hg => ?_
          have hv : ∀ g : Fin 8, g ∉ blockI → g ≠ 6 → g ≠ 7 → rowA g = 3 := by decide
          obtain ⟨hg7,hgG⟩ := Finset.mem_erase.mp hg
          exact hv g (fun hm => Finset.disjoint_left.mp hdisj hgG hm) (fun ht => h6 (ht ▸ hg)) hg7
        _ = _ := by simp [nsmul_eq_mul]
    omega
  have hempty : tail.erase 6 = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨g,hg⟩
    have hval : naturalValue rowA (tail.erase 6) = 0 := by
      have hs := Finset.sum_erase_add tail rowA hkeep
      change naturalValue rowA (tail.erase 6) + rowA 6 = naturalValue rowA tail at hs
      have hc : rowA 6 = 4 := by decide
      omega
    have hgval : rowA g ≤ naturalValue rowA (tail.erase 6) :=
      Finset.single_le_sum (fun g _ => Nat.zero_le (rowA g)) hg
    have hpos : ∀ g : Fin 8, 0 < rowA g := by decide
    have hpg := hpos g
    omega
  have ht : tail = {6} := by
    rw [← Finset.insert_erase hkeep,hempty]
    rfl
  rw [← Finset.insert_erase h7]
  change insert (7 : Fin 8) tail = blockK
  rw [ht]
  decide

private theorem complete_partition_groups (G S T : Finset (Fin 8))
    (hG : naturalValue rowA G = 9) (hS : naturalValue rowA S = 9) (hT : naturalValue rowA T = 9)
    (hGS : Disjoint G S) (hGT : Disjoint G T) (hST : Disjoint S T)
    (hcover : G ∪ S ∪ T = Finset.univ) : G ∈ groups := by
  have hone (i : Fin 8) : i ∈ G ∨ i ∈ S ∨ i ∈ T := by
    have h : i ∈ G ∪ S ∪ T := by rw [hcover]; exact Finset.mem_univ i
    simp only [Finset.mem_union] at h
    tauto
  have hI0 : (7 : Fin 8) ∉ blockI := by decide
  have comp (A : Finset (Fin 8)) (hdA : Disjoint A blockI) (hdB : Disjoint A blockK)
      (hEq : A ∪ blockI ∪ blockK = Finset.univ) : A = blockJ := by
    have hJ : blockJ = Finset.univ \ (blockI ∪ blockK) := by decide
    rw [hJ]
    ext g
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union]
    constructor
    · exact fun hg h => h.elim (Finset.disjoint_left.mp hdA hg) (Finset.disjoint_left.mp hdB hg)
    · intro hg
      have hm : g ∈ A ∪ blockI ∪ blockK := by rw [hEq]; exact Finset.mem_univ g
      simp only [Finset.mem_union] at hm
      tauto
  rcases hone 0 with h | h | h
  · simp [groups,contain_seven G hG h]
  · have he := contain_seven S hS h
    subst S
    rcases hone 7 with h' | h' | h'
    · simp [groups,contain_five G hG h' hGS]
    · exact (hI0 h').elim
    · have hk := contain_five T hT h' hST.symm
      subst T
      have hh : G = blockJ := comp G hGS hGT hcover
      simp [groups,hh]
  · have he := contain_seven T hT h
    subst T
    rcases hone 7 with h' | h' | h'
    · simp [groups,contain_five G hG h' hGT]
    · have hk := contain_five S hS h' hST
      subst S
      have hu : G ∪ blockI ∪ blockK = Finset.univ := by
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
      have hh : G = blockJ := comp G hGT hGS hu
      simp [groups,hh]
    · exact (hI0 h').elim

private theorem groups_certificate :
    ∀ G ∈ groups, ¬ paysTwo rowB 10 (Finset.univ \ G) := by
  intro G hG
  simp only [groups, Finset.mem_insert, Finset.mem_singleton] at hG
  rcases hG with rfl | rfl | rfl <;> decide

private theorem upper_certificate (G : Finset (Fin 8))
    (hG : 9 ≤ naturalValue rowA G) (h : paysTwo rowA 9 (Finset.univ \ G)) :
    ¬ paysTwo rowB 10 (Finset.univ \ G) := by
  obtain ⟨S,hS,hsA,hsB⟩ := h
  have hsub := Finset.mem_powerset.mp hS
  have htotal : naturalValue rowA Finset.univ = 27 := by decide
  have hsum1 : naturalValue rowA (Finset.univ \ G) + naturalValue rowA G =
      naturalValue rowA Finset.univ := Finset.sum_sdiff (Finset.subset_univ _)
  have hsum2 : naturalValue rowA ((Finset.univ \ G) \ S) + naturalValue rowA S =
      naturalValue rowA (Finset.univ \ G) := Finset.sum_sdiff hsub
  let T := (Finset.univ \ G) \ S
  have hGT : Disjoint G T := by
    apply Finset.disjoint_left.mpr
    exact fun g hg ht => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ht).1).2 hg
  have hGS : Disjoint G S := by
    apply Finset.disjoint_left.mpr
    exact fun g hg hs => (Finset.mem_sdiff.mp (hsub hs)).2 hg
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hall : G ∪ S ∪ T = Finset.univ := by
    ext g
    simp only [T,Finset.mem_union,Finset.mem_univ,Finset.mem_sdiff,true_and,iff_true]
    tauto
  have heqT : naturalValue rowA T = 9 := by dsimp [T]; omega
  exact groups_certificate G (complete_partition_groups G S T (by omega) (by omega)
    heqT hGS hGT hST hall)

/-- The eight-good two-type instance rules out every deterministic online
guarantee above 9/10 at horizon three. -/
theorem three_arrival_upper_instance :
    ∃ v : Fin 2 → Fin 8 → ℝ, (∀ t g, 0 ≤ v t g) ∧
      ∀ a > (9 / 10 : ℝ), ∀ p : Policy 8 2 3,
        ¬ p.Guarantees v (fun t => a * maximinShare (v t) 3 (by decide)) Finset.univ := by
  refine ⟨realValuation, ?_, ?_⟩
  · intro t g
    unfold realValuation
    split <;> positivity
  intro a ha p hp
  have hA (G : Finset (Fin 8))
      (h : a * maximinShare (realValuation 0) 3 (by decide) ≤ bundleValue (realValuation 0) G) :
      9 ≤ naturalValue rowA G := by
    rw [witness_mms_A, valueA] at h
    by_contra hn
    have hn' : naturalValue rowA G < 9 := lt_of_not_ge hn
    have hr : (naturalValue rowA G : ℝ) ≤ 8 := by exact_mod_cast (Nat.lt_succ_iff.mp hn')
    linarith
  have hB (G : Finset (Fin 8))
      (h : a * maximinShare (realValuation 1) 3 (by decide) ≤ bundleValue (realValuation 1) G) :
      10 ≤ naturalValue rowB G := by
    rw [witness_mms_B, valueB] at h
    by_contra hn
    have hn' : naturalValue rowB G < 10 := lt_of_not_ge hn
    have hr : (naturalValue rowB G : ℝ) ≤ 9 := by exact_mod_cast (Nat.lt_succ_iff.mp hn')
    linarith
  cases p with
  | step bundle next =>
    obtain ⟨_, hpay, hcont⟩ := hp 0
    let G := bundle 0
    let R := Finset.univ \ G
    have hf : 9 ≤ naturalValue rowA G := hA G hpay
    have htwo (t : Fin 2) (v : Fin 8 → ℕ) (q : ℕ)
        (hpayNat : ∀ S, a * maximinShare (realValuation t) 3 (by decide) ≤
          bundleValue (realValuation t) S → q ≤ naturalValue v S) :
        paysTwo v q R := by
      cases hnext : next 0 with
      | step bundle₂ next₂ =>
        rw [hnext] at hcont
        obtain ⟨hsub, hval, hcont₂⟩ := hcont t
        cases hnext₂ : next₂ t with
        | step bundle₃ done =>
          rw [hnext₂] at hcont₂
          obtain ⟨hsub₃, hval₃, _⟩ := hcont₂ t
          refine ⟨bundle₂ t, Finset.mem_powerset.mpr hsub, hpayNat _ hval, ?_⟩
          exact (hpayNat _ hval₃).trans
            (Finset.sum_le_sum_of_subset_of_nonneg hsub₃ fun _ _ _ => Nat.zero_le _)
    exact upper_certificate G hf
      (htwo 0 rowA 9 hA) (htwo 1 rowB 10 hB)

/-- The row-deletion coefficient is sharp for the original three-way MMS,
using the same eight goods as the three-arrival obstruction. -/
theorem choosing_row_nine_tenths_sharp :
    ∃ (v : Fin 8 → ℝ) (rows : Fin 8 → Fin 3), (∀ g, 0 ≤ v g) ∧
      maximinShare v 3 (by decide) = 10 ∧
      ∀ i : Fin 3, ∀ q > (9 : ℝ),
        ¬ HasPaymentPartition v (Finset.univ \ Finset.univ.filter (fun g => rows g = i)) 2 q := by
  refine ⟨realValuation 1,partitionA,fun g => ?_,witness_mms_B,?_⟩
  · change 0 ≤ (rowB g : ℝ)
    positivity
  · intro i q hq hp
    let G := (Finset.univ : Finset (Fin 8)).filter (fun g => partitionA g = i)
    have hgroups : ∀ i : Fin 3,
        (Finset.univ.filter (fun g => partitionA g = i)) ∈ groups := by decide
    obtain ⟨B,hB,hBA,hBB⟩ := paymentPartition_two_cut hp
    have hlarge (S : Finset (Fin 8)) (h : q ≤ bundleValue (realValuation 1) S) :
        10 ≤ naturalValue rowB S := by
      rw [valueB] at h
      by_contra hlt
      have hnat : naturalValue rowB S ≤ 9 := Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
      have hℝ : (naturalValue rowB S : ℝ) ≤ 9 := by exact_mod_cast hnat
      linarith
    exact groups_certificate G (hgroups i)
      ⟨B,Finset.mem_powerset.mpr hB,hlarge B hBA,hlarge _ hBB⟩

end OnlineMMS
