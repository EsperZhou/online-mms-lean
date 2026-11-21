import OnlineMMS.BinarySmall
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Combinatorics.SetFamily.LYM

namespace OnlineMMS.BinaryRuntime

variable {G : Type*} [DecidableEq G]

private def firstComparable (f : G → ApprovalPattern) (L : List G) : Option (G × G) :=
  (L.product L).find? (fun (a, b) => decide (a ≠ b ∧ f a ⊆ f b))

private def removePair (a b : G) (L : List G) : List G :=
  L.filter fun g => decide (g ≠ a ∧ g ≠ b)

private theorem removePair_finset (a b : G) (L : List G) :
    (removePair a b L).toFinset = L.toFinset \ {a, b} := by
  ext g
  simp [removePair, and_assoc]

/-- Candidate selections of the required size in the terminal antichain. -/
def halfCandidates (L : List G) : List (List G) :=
  L.sublistsLen (L.length / 2)

private def firstBalanced (f : G → ApprovalPattern) (L : List G) : Option (List G) :=
  (halfCandidates L).find? fun Y => by
    letI : Decidable (IsBalancedHalf f L.toFinset Y.toFinset) := by
      unfold IsBalancedHalf
      infer_instance
    exact decide (IsBalancedHalf f L.toFinset Y.toFinset)

/-- Repeatedly strip a comparable pair and keep its smaller pattern. The work
    counter charges all candidate-pair tests, a linear deletion pass and, at
    the terminal antichain, the exhaustive scan of half-size subsets. A terminal
    candidate is charged a quadratic bound for constructing its finite set
    and testing its five cardinality constraints. -/
def smallGreedy (f : G → ApprovalPattern) : ℕ → List G → List G × ℕ
  | 0, _ => ([], 1)
  | fuel + 1, L =>
    let scans := L.length * L.length + L.length + 1
    match firstComparable f L with
    | some (a, b) =>
      let out := smallGreedy f fuel (removePair a b L)
      (a :: out.1, scans + out.2)
    | none => ((firstBalanced f L).getD [],
        scans + (L.length + 1)^2 * (L.length.choose (L.length / 2)))

private theorem no_pair_of_none (f : G → ApprovalPattern) (L : List G)
    (h : firstComparable f L = none) :
    ¬ ∃ a ∈ L.toFinset, ∃ b ∈ L.toFinset, a ≠ b ∧ f a ⊆ f b := by
  rintro ⟨a, ha, b, hb, hne, hsub⟩
  have hm : (a, b) ∈ L.product L :=
    List.mem_product.mpr ⟨List.mem_toFinset.mp ha, List.mem_toFinset.mp hb⟩
  have hn := (List.find?_eq_none.mp h) (a, b) hm
  exact hn (by simpa using And.intro hne hsub)

private theorem firstBalanced_spec (f : G → ApprovalPattern) (L : List G)
    (hL : L.Nodup) (h : firstComparable f L = none) :
    IsBalancedHalf f L.toFinset ((firstBalanced f L).getD []).toFinset := by
  obtain ⟨Y, hY⟩ := balanced_half_no_pair f L.toFinset (no_pair_of_none f L h)
  let candidate := L.filter (fun a => decide (a ∈ Y))
  have heq : candidate.toFinset = Y := by
    ext a
    simp only [candidate, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact and_iff_right_of_imp (fun hm => List.mem_toFinset.mp (hY.1 hm))
  have hc : candidate.Nodup := hL.filter _
  have hmem : candidate ∈ halfCandidates L := List.mem_sublistsLen.mpr
    ⟨List.filter_sublist, by
      rw [← List.toFinset_card_of_nodup hc, heq, hY.2.1, List.toFinset_card_of_nodup hL]⟩
  cases hs : firstBalanced f L with
  | none =>
    have hn := (List.find?_eq_none.mp hs) candidate hmem
    exact (hn (by simpa only [decide_eq_true_eq, heq] using hY)).elim
  | some out =>
    have hz := List.find?_some hs
    simpa only [hs, Option.getD_some, decide_eq_true_eq] using hz

/-- The concrete comparable-pair routine produces the required balanced half. -/
theorem smallGreedy_spec (f : G → ApprovalPattern) (fuel : ℕ) (L : List G)
    (hL : L.Nodup) (hfuel : L.length < fuel) :
    IsBalancedHalf f L.toFinset (smallGreedy f fuel L).1.toFinset := by
  induction fuel generalizing L with
  | zero => omega
  | succ fuel ih =>
    cases hs : firstComparable f L with
    | none =>
      simpa only [smallGreedy, hs] using firstBalanced_spec f L hL hs
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hm := List.mem_of_find?_eq_some hs
      obtain ⟨ha, hb⟩ := List.mem_product.mp hm
      have hpair := List.find?_some hs
      have hpair' : a ≠ b ∧ f a ⊆ f b := by simpa only [decide_eq_true_eq] using hpair
      have hshort : (removePair a b L).length < L.length := by
        apply lt_of_le_of_ne (List.length_filter_le _ _)
        intro he
        have hz := List.length_filter_eq_length_iff.mp he a ha
        simp at hz
      have hrec := ih (removePair a b L) (hL.filter _) (by omega)
      rw [removePair_finset] at hrec
      simpa only [smallGreedy, hs, List.toFinset_cons] using
        balanced_half_step f L.toFinset a b (List.mem_toFinset.mpr ha)
          (List.mem_toFinset.mpr hb) hpair'.1 hpair'.2 _ hrec

/-- With no comparable pair, the five-coordinate antichain has at most ten goods. -/
theorem terminal_length_le (f : G → ApprovalPattern) (L : List G) (hL : L.Nodup)
    (hn : ¬ ∃ a ∈ L.toFinset, ∃ b ∈ L.toFinset, a ≠ b ∧ f a ⊆ f b) : L.length ≤ 10 := by
  rw [← List.toFinset_card_of_nodup hL]
  have hi := Finset.card_image_of_injOn (pattern_injective_of_no_pair f L.toFinset hn)
  rw [← hi]
  have hanti : IsAntichain (· ⊆ ·) (L.toFinset.image f).toSet := by
    intro A hA B hB hneq hsub
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    exact hn ⟨a, ha, b, hb, fun h => hneq (congrArg f h), hsub⟩
  calc
    _ ≤ (Fintype.card (Fin 5)).choose (Fintype.card (Fin 5) / 2) := hanti.sperner
    _ = 10 := by decide

private theorem central_choose_ten (n : ℕ) (hn : n ≤ 10) :
    n.choose (n / 2) ≤ 252 := by
  interval_cases n <;> decide

/-- The residual search considers at most 252 half-size selections. -/
theorem terminal_candidates_le (f : G → ApprovalPattern) (L : List G) (hL : L.Nodup)
    (hn : ¬ ∃ a ∈ L.toFinset, ∃ b ∈ L.toFinset, a ≠ b ∧ f a ⊆ f b) :
    (halfCandidates L).length ≤ 252 := by
  simpa only [halfCandidates, List.length_sublistsLen] using
    central_choose_ten L.length (terminal_length_le f L hL hn)

/-- Cubic pair-scan work plus a constant bound on the final exhaustive scan. -/
theorem smallGreedy_cost (f : G → ApprovalPattern) (fuel m : ℕ) (L : List G)
    (hL : L.Nodup) (hm : L.length ≤ m) :
    (smallGreedy f fuel L).2 ≤ fuel * (m * m + m + 1) + 11^2 * 252 + 1 := by
  induction fuel generalizing L with
  | zero => simp [smallGreedy]
  | succ fuel ih =>
    have hsq := Nat.mul_le_mul hm hm
    cases hs : firstComparable f L with
    | none =>
      have hn := terminal_length_le f L hL (no_pair_of_none f L hs)
      have hprod : (L.length + 1)^2 * L.length.choose (L.length / 2) ≤ 11^2 * 252 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (central_choose_ten L.length hn)
      simp only [smallGreedy, hs]
      change _ ≤ (fuel + 1) * (m * m + m + 1) + 11^2 * 252 + 1
      rw [Nat.add_mul, one_mul]
      omega
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hnext : (removePair a b L).length ≤ m := (List.length_filter_le _ _).trans hm
      have hrec := ih (removePair a b L) (hL.filter _) hnext
      simp only [smallGreedy, hs]
      change _ ≤ (fuel + 1) * (m * m + m + 1) + 11^2 * 252 + 1
      rw [Nat.add_mul, one_mul]
      omega

private def paddedPattern {m k : ℕ} (S : Fin (k + 1) → Finset (Fin m))
    (first : Fin (k + 1)) (g : Fin m) : ApprovalPattern :=
  Finset.univ.filter fun i : Fin 5 =>
    if hi : i.val < k then g ∈ S (first.succAbove ⟨i.val, hi⟩) else False

private theorem paddedPattern_spec {m k : ℕ} (hk : k + 1 ≤ 6)
    (S : Fin (k + 1) → Finset (Fin m)) (first t : Fin (k + 1)) (ht : t ≠ first) :
    ∃ i : Fin 5, ∀ g, i ∈ paddedPattern S first g ↔ g ∈ S t := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq ht
  let i : Fin 5 := ⟨j.val, by have h := j.isLt; omega⟩
  refine ⟨i, fun g => ?_⟩
  simp only [paddedPattern, Finset.mem_filter, Finset.mem_univ, true_and, dif_pos j.isLt, i, hj]

private def smallItems {m : ℕ} (V : Finset (Fin m)) : List (Fin m) :=
  (List.finRange m).filter fun a => decide (a ∈ V)

/-- The concrete left-to-right small-type allocation rule. -/
def smallBundle {m : ℕ} : {k : ℕ} → (Fin k → Finset (Fin m)) →
    Fin k → Finset (Fin m)
  | 0, _, first => first.elim0
  | _ + 1, S, first =>
    (smallGreedy (paddedPattern S first) (m + 1) (smallItems (S first))).1.toFinset

/-- The computed small-type bundle pays both full MMS demands. -/
theorem smallBundle_spec {m k : ℕ} (hk : k ≤ 6)
    (S : Fin k → Finset (Fin m)) (first : Fin k) :
    smallBundle S first ⊆ S first ∧
      binaryDemand (S first).card 1 ≤ (smallBundle S first).card ∧
      ∀ t, binaryDemand (S t).card 1 ≤ (S t \ smallBundle S first).card := by
  cases k with
  | zero => exact first.elim0
  | succ k =>
    let L := smallItems (S first)
    have hL : L.Nodup := (List.nodup_finRange _).filter _
    have hlen : L.length ≤ m := (List.length_filter_le _ _).trans_eq List.length_finRange
    have hset : L.toFinset = S first := by ext a; simp [L, smallItems]
    have hs := smallGreedy_spec (paddedPattern S first) (m + 1) L hL (by omega)
    rw [hset] at hs
    exact binary_small_bundle_of_balanced S first (paddedPattern S first)
      (fun t => paddedPattern_spec hk S first t) _ hs

/-- The computed small-type policy evaluated at the original MMS benchmark. -/
theorem smallPolicy_guarantees {m k : ℕ} (hk : k ≤ 6)
    (S : Fin k → Finset (Fin m)) :
    (binaryPolicy (smallBundle S)).Guarantees (fun t => approvalValue (S t))
      (fun t => maximinShare (approvalValue (S t)) 2 (by decide)) Finset.univ := by
  simpa using binaryPolicy_guarantees (p := 1) (by decide) S _ (smallBundle_spec hk S)

/-- Work including pattern checks, indexing the approved items, emitting the
    chosen bundle, and returning the complement. We charge at most (m+1)
    row-membership work per scan unit when the approval rows are lists.
    The fixed factor accounts for the five coordinates. -/
def smallPolicyCost {m : ℕ} : {k : ℕ} → (Fin k → Finset (Fin m)) → Fin k → ℕ
  | 0, _, first => first.elim0
  | _ + 1, S, first =>
    10 * (m + 1) * (smallGreedy (paddedPattern S first) (m + 1) (smallItems (S first))).2 +
      3 * (m + 1)^2

theorem smallPolicyCost_le {m k : ℕ} (S : Fin k → Finset (Fin m)) (first : Fin k) :
    smallPolicyCost S first ≤
      10 * (m + 1) * ((m + 1) * (m*m + m + 1) + 11^2 * 252 + 1) +
      3 * (m + 1)^2 := by
  cases k with
  | zero => exact first.elim0
  | succ k =>
    have hlen : (smallItems (S first)).length ≤ m :=
      (List.length_filter_le _ _).trans_eq List.length_finRange
    have h := smallGreedy_cost (paddedPattern S first) (m + 1) m (smallItems (S first))
      ((List.nodup_finRange _).filter _) hlen
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

end OnlineMMS.BinaryRuntime
