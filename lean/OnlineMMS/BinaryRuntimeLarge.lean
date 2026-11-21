import OnlineMMS.BinaryLarge
import OnlineMMS.BinaryRuntimeGraph
import OnlineMMS.BinaryRuntimePairs

namespace OnlineMMS.BinaryRuntime

/-- Integer ceiling of the binary MMS divided by the pair parameter. -/
def demandCount (a p : ℕ) : ℕ :=
  if a / 2 = 0 then 0 else (a / 2 - 1) / p + 1

theorem demandCount_eq (a : ℕ) {p : ℕ} (hp : 0 < p) :
    demandCount a p = binaryDemand a p := by
  by_cases h : a / 2 = 0
  · simp only [demandCount, if_pos h]
    have hd := binaryDemand_le_half a hp
    omega
  · let u := (a / 2 - 1) / p
    have hl : p * u ≤ a / 2 - 1 := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp).mp le_rfl
    have hu : a / 2 - 1 < p * (u + 1) := by
      rw [mul_comm]
      exact (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
    have hpay := binaryDemand_pays a hp
    rw [demandCount, if_neg h]
    change u + 1 = binaryDemand a p
    apply le_antisymm
    · by_contra! hlt
      have hh := Nat.mul_le_mul_left p (show binaryDemand a p ≤ u by omega)
      omega
    · by_contra! hlt
      have hh := binaryDemand_min a hp hlt
      omega

private def orderedItems {m : ℕ} (V : Finset (Fin m)) : List (Fin m) :=
  (List.finRange m).filter fun a => decide (a ∈ V)

private theorem orderedItems_nodup {m : ℕ} (V : Finset (Fin m)) :
    (orderedItems V).Nodup :=
  (List.nodup_finRange m).filter _

@[simp] private theorem orderedItems_toFinset {m : ℕ} (V : Finset (Fin m)) :
    (orderedItems V).toFinset = V := by
  ext a
  simp [orderedItems]

private theorem orderedItems_length {m : ℕ} (V : Finset (Fin m)) :
    (orderedItems V).length = V.card := by
  rw [← List.toFinset_card_of_nodup (orderedItems_nodup V), orderedItems_toFinset]

private def designatedPairs {m : ℕ} (p : ℕ) (V : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  (rowPairs (demandCount V.card p) (orderedItems V)).toFinset

private theorem designatedPairs_spec {m p : ℕ} (hp : 0 < p) (V : Finset (Fin m)) :
    (designatedPairs p V).card = binaryDemand V.card p ∧
      (↑(designatedPairs p V) : Set (Finset (Fin m))).Pairwise Disjoint ∧
      ∀ e ∈ designatedPairs p V, e ⊆ V ∧ e.card = 2 := by
  have hhalf := binaryDemand_le_half V.card hp
  have hh : 2 * demandCount V.card p ≤ (orderedItems V).length := by
    rw [orderedItems_length, demandCount_eq _ hp]
    omega
  have hs := rowPairs_spec (demandCount V.card p) (orderedItems V) (orderedItems_nodup _) hh
  simpa only [designatedPairs, orderedItems_toFinset, demandCount_eq _ hp] using hs

private def edgeQuery {m : ℕ} (E : Finset (Finset (Fin m))) (a b : Fin m) : Bool :=
  decide (a ≠ b ∧ ({a, b} : Finset (Fin m)) ∈ E)

private def graphAnswer {m : ℕ} (E : Finset (Finset (Fin m))) (V : Finset (Fin m)) :
    List (Fin m) × ℕ :=
  graphGreedy (edgeQuery E) V.card (orderedItems V)

private def takeItems {m : ℕ} (ℓ : ℕ) (V : Finset (Fin m)) : Finset (Fin m) :=
  ((orderedItems V).take ℓ).toFinset

private theorem takeItems_spec {m ℓ : ℕ} (V : Finset (Fin m)) (h : ℓ ≤ V.card) :
    takeItems ℓ V ⊆ V ∧ (takeItems ℓ V).card = ℓ := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [← orderedItems_toFinset V]
    exact List.mem_toFinset.mpr (List.take_subset _ _ (List.mem_toFinset.mp ha))
  · unfold takeItems
    have hn : ((orderedItems V).take ℓ).Nodup := (orderedItems_nodup V).take
    rw [List.toFinset_card_of_nodup hn, List.length_take,
      orderedItems_length, min_eq_left h]

private def inputEdges {m k : ℕ} (p : ℕ) (S : Fin k → Finset (Fin m)) (first : Fin k) :
    Finset (Finset (Fin m)) :=
  let ℓ := demandCount (S first).card p
  let active := Finset.univ.filter fun t : Fin k =>
    t ≠ first ∧ (S t).card - ℓ < demandCount (S t).card p
  (active.biUnion fun t => designatedPairs p (S t)).filter (· ⊆ S first)

/-- Executable large-type binary rule with increasing item indices for ties. -/
def largeBundle {m k : ℕ} (p : ℕ) (S : Fin k → Finset (Fin m)) (first : Fin k) :
    Finset (Fin m) :=
  let ℓ := demandCount (S first).card p
  if ℓ ≤ 1 then takeItems ℓ (S first)
  else takeItems ℓ (graphAnswer (inputEdges p S first) (S first)).1.toFinset

/-- The specific computed large-type bundle simultaneously pays all demands. -/
theorem largeBundle_spec {m k p : ℕ} (hp : 2 ≤ p)
    (hmax : ∀ q : ℕ, 1 + (q + q).choose 2 ≤ k → q ≤ p)
    (S : Fin k → Finset (Fin m)) (first : Fin k) :
    largeBundle p S first ⊆ S first ∧
      binaryDemand (S first).card p ≤ (largeBundle p S first).card ∧
      ∀ t, binaryDemand (S t).card p ≤ (S t \ largeBundle p S first).card := by
  have hp0 : 0 < p := by omega
  have hpick (E : Finset (Finset (Fin m))) (V : Finset (Fin m))
      (hE : ∀ e ∈ E, e ⊆ V ∧ e.card = 2) (z : ℕ)
      (hz : (z : ℝ) * ((V.card : ℝ) + 2 * (E.card : ℝ)) < (V.card : ℝ) ^ 2) :
      let I := (graphAnswer E V).1.toFinset
      I ⊆ V ∧ PairIndependent E I ∧ z + 1 ≤ I.card := by
    have hstrict : (z : ℝ) * (((orderedItems V).toFinset.card : ℝ) + 2 * (E.card : ℝ)) <
        ((orderedItems V).toFinset.card : ℝ) ^ 2 := by simpa using hz
    have hs := graphGreedy_threshold E (edgeQuery E) (fun a b => by simp [edgeQuery])
      (orderedItems V) (orderedItems_nodup _) (by simpa using hE) hstrict
    simp only [orderedItems_toFinset, orderedItems_length] at hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hs := binary_large_bundle_via hp hmax S first (fun t => designatedPairs p (S t))
    (fun t => (designatedPairs_spec hp0 (S t)).1)
    (fun t => (designatedPairs_spec hp0 (S t)).2.1)
    (fun t => (designatedPairs_spec hp0 (S t)).2.2)
    (fun E V => (graphAnswer E V).1.toFinset) hpick
    (takeItems (binaryDemand (S first).card p)) takeItems_spec
  simpa only [largeBundle, inputEdges, demandCount_eq _ hp0] using hs

/-- Total scan units for the graph stage on the graph that the policy constructs. -/
theorem largeBundle_graphCost {m k : ℕ} (p : ℕ) (S : Fin k → Finset (Fin m)) (first : Fin k) :
    (graphAnswer (inputEdges p S first) (S first)).2 ≤ (m + 1) ^ 3 := by
  unfold graphAnswer
  have hV : (S first).card ≤ m := by simpa using Finset.card_le_univ (S first)
  have hcount := graphGreedy_cost (edgeQuery (inputEdges p S first)) m (S first).card
    (orderedItems (S first)) (by simpa only [orderedItems_length] using hV)
  have hmul := Nat.mul_le_mul_right (m * m + 3 * m + 1) hV
  exact hcount.trans (by nlinarith)

/-- The pair count as an integer product, used in the bounded parameter scan. -/
private theorem pairCountFormula (q : ℕ) : (q + q).choose 2 = q * (q + q - 1) := by
  rw [Nat.choose_two_right, ← two_mul q, mul_assoc,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2), two_mul]

/-- Scan at most `k` integer candidates for the manuscript's pair parameter. -/
def parameterCount (k : ℕ) : ℕ :=
  Nat.findGreatest (fun q => 1 + q * (q + q - 1) ≤ k) k

theorem parameterCount_eq {k : ℕ} (hk : 7 ≤ k) : parameterCount k = pairParameter k := by
  obtain ⟨_, hvalid, hmax⟩ := pairParameter_spec hk
  let P := fun q : ℕ => 1 + q * (q + q - 1) ≤ k
  have hb {q : ℕ} (h : P q) : q ≤ k := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · omega
    · have hm := Nat.mul_le_mul_left q (show 1 ≤ q + q - 1 by omega)
      change 1 + q * (q + q - 1) ≤ k at h
      omega
  have hv : P (pairParameter k) := by simpa only [P, pairCountFormula] using hvalid
  have hs : P (parameterCount k) := Nat.findGreatest_spec (hb hv) hv
  exact le_antisymm (hmax _ (by simpa only [P, pairCountFormula] using hs))
    (Nat.le_findGreatest (hb hv) hv)

/-- The computed large-type policy evaluated at the original MMS benchmark. -/
theorem largePolicy_guarantees {m k : ℕ} (hk : 7 ≤ k) (S : Fin k → Finset (Fin m)) :
    (binaryPolicy (largeBundle (parameterCount k) S)).Guarantees (fun t => approvalValue (S t))
      (fun t => (1 / (pairParameter k : ℝ)) * maximinShare (approvalValue (S t)) 2 (by decide))
      Finset.univ := by
  rw [parameterCount_eq hk]
  obtain ⟨hp, _, hmax⟩ := pairParameter_spec hk
  exact binaryPolicy_guarantees (by omega) S _ (largeBundle_spec hp hmax S)

/-- Pair visits over all rows, counting inactive rows as an upper bound. -/
private def pairSetupCost {m k : ℕ} (p : ℕ) (S : Fin k → Finset (Fin m)) : ℕ :=
  ∑ t, rowPairsCost (Fin m) (demandCount (S t).card p) (orderedItems (S t))

/-- Conservative word-scan charge for the concrete implementation.
    The parameter scan uses at most `k` candidate checks. Row membership
    may scan a whole row per item. The edge union may compare every pair
    produced with every other pair, and visibility may scan the first row.
    Each graph-stage adjacency query may scan the edge set. The final term
    permits scanning and deduplicating the selected items and returning the
    complement to the second arrival. -/
def largePolicyCost {m k : ℕ} (S : Fin k → Finset (Fin m)) (first : Fin k) : ℕ :=
  let p := parameterCount k
  let E := inputEdges p S first
  let pairs := pairSetupCost p S
  k + 1 + (k + 1) * (m + 1)^2 + (pairs + 1)^2 + pairs * (m + 1) +
    (graphAnswer E (S first)).2 * (E.card + 1) + 3 * (m + 1)^2

theorem largePolicyCost_le {m k : ℕ} (hk : 7 ≤ k) (S : Fin k → Finset (Fin m))
    (first : Fin k) :
    largePolicyCost S first ≤
      k + 1 + (k + 1) * (m + 1)^2 + (k * (m + 1) + 1)^2 +
      (k * (m + 1)) * (m + 1) + (m + 1)^3 * (k * m + 1) + 3 * (m + 1)^2 := by
  let p := parameterCount k
  have hp : 0 < p := by
    dsimp [p]
    rw [parameterCount_eq hk]
    have h := (pairParameter_spec hk).1
    omega
  have hrow (t : Fin k) : demandCount (S t).card p ≤ m := by
    rw [demandCount_eq _ hp]
    exact (binaryDemand_le_half _ hp).trans
      ((Nat.div_le_self _ _).trans ((by simpa using Finset.card_le_univ (S t))))
  have hsetup : pairSetupCost p S ≤ k * (m + 1) := by
    unfold pairSetupCost
    calc
      _ ≤ ∑ _t : Fin k, (m + 1) :=
        Finset.sum_le_sum (fun t _ => (rowPairsCost_le _ _).trans (Nat.succ_le_succ (hrow t)))
      _ = _ := by simp
  have hEdges : (inputEdges p S first).card ≤ k * m := by
    unfold inputEdges
    apply (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans _)
    calc
      _ ≤ ∑ t : Fin k, (designatedPairs p (S t)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ∑ _t : Fin k, m := Finset.sum_le_sum (fun t _ => by
        rw [(designatedPairs_spec hp _).1, ← demandCount_eq _ hp]
        exact hrow t)
      _ = _ := by simp
  have hGraph := largeBundle_graphCost p S first
  have h2 : (pairSetupCost p S + 1)^2 ≤ (k * (m + 1) + 1)^2 :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hsetup) 2
  have h3 := Nat.mul_le_mul_right (m + 1) hsetup
  have h4 : (graphAnswer (inputEdges p S first) (S first)).2 * ((inputEdges p S first).card + 1) ≤
      (m + 1)^3 * (k * m + 1) :=
    Nat.mul_le_mul hGraph (Nat.succ_le_succ hEdges)
  change k + 1 + (k + 1) * (m + 1)^2 + (pairSetupCost p S + 1)^2 +
    pairSetupCost p S * (m + 1) +
    (graphAnswer (inputEdges p S first) (S first)).2 * ((inputEdges p S first).card + 1) +
    3 * (m + 1)^2 ≤ _
  omega

end OnlineMMS.BinaryRuntime
