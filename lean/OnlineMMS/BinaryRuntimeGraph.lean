import OnlineMMS.BinaryGraph
import Mathlib.Data.List.MinMax

namespace OnlineMMS

namespace BinaryRuntime

variable {G : Type*} [DecidableEq G]

/-- Parts of one round of the minimum-degree algorithm, implemented by scans
    of the current list. Each adjacency query is a word operation in the
    adjacency-matrix model. -/
private def graphScores (adj : G → G → Bool) (L : List G) : List (G × ℕ) :=
  L.map fun a => (a, L.countP (adj a))

private def graphPrune (adj : G → G → Bool) (v : G) (L : List G) : List G :=
  L.filter fun b => decide (b ≠ v) && !(adj v b)

/-- Choose a minimum-degree vertex, delete its closed neighborhood, and repeat.
    One round charges a degree-counter operation and adjacency query per pair
    of current vertices, a score construction and comparison per vertex, one
    prune visit per vertex, and one fixed control operation. The returned count
    is in these scan units, with a constant amount of word work per unit. -/
def graphGreedy (adj : G → G → Bool) : ℕ → List G → List G × ℕ
  | 0, _ => ([], 1)
  | fuel + 1, L =>
    match (graphScores adj L).argmin Prod.snd with
    | none => ([], 1)
    | some (v, _) =>
      let next := graphGreedy adj fuel (graphPrune adj v L)
      (v :: next.1, L.length * L.length + 3 * L.length + 1 + next.2)

private theorem graphScore_eq (E : Finset (Finset G)) (adj : G → G → Bool)
    (hadj : ∀ a b, adj a b = true ↔ a ≠ b ∧ ({a, b} : Finset G) ∈ E)
    (L : List G) (hL : L.Nodup) (a : G) :
    L.countP (adj a) = pairDegree E L.toFinset a := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext b
  simp [pairNeighbors, hadj]

private theorem graphPrune_toFinset (E : Finset (Finset G)) (adj : G → G → Bool)
    (hadj : ∀ a b, adj a b = true ↔ a ≠ b ∧ ({a, b} : Finset G) ∈ E)
    (L : List G) (v : G) :
    (graphPrune adj v L).toFinset = pairResidual E L.toFinset v := by
  ext b
  by_cases h : b = v
  · simp [graphPrune, pairResidual, h]
  · have hfalse : adj v b = false ↔ ({v, b} : Finset G) ∉ E := by
      rw [← Bool.not_eq_true, hadj]
      simp [Ne.symm h]
    simp [graphPrune, pairResidual, pairNeighbors, h, Ne.symm h, hfalse]
    tauto

private theorem graphPrune_shorter (adj : G → G → Bool) {L : List G} {v : G}
    (hv : v ∈ L) : (graphPrune adj v L).length < L.length := by
  unfold graphPrune
  have hle := List.length_filter_le (fun b => decide (b ≠ v) && !(adj v b)) L
  apply lt_of_le_of_ne hle
  intro he
  have h := List.length_filter_eq_length_iff.mp he _ hv
  simp at h

/-- The returned vertices are independent and meet the Caro--Wei bound. -/
theorem graphGreedy_spec (E : Finset (Finset G)) (adj : G → G → Bool)
    (hadj : ∀ a b, adj a b = true ↔ a ≠ b ∧ ({a, b} : Finset G) ∈ E)
    (fuel : ℕ) (L : List G) (hL : L.Nodup) (hfuel : L.length ≤ fuel) :
    let I := (graphGreedy adj fuel L).1.toFinset
    I ⊆ L.toFinset ∧ PairIndependent E I ∧
      (∑ a ∈ L.toFinset, 1 / ((pairDegree E L.toFinset a : ℝ) + 1)) ≤ (I.card : ℝ) := by
  induction fuel generalizing L with
  | zero =>
    have hnil : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hfuel)
    subst L
    simp [graphGreedy, PairIndependent]
  | succ fuel ih =>
    cases hs : (graphScores adj L).argmin Prod.snd with
    | none =>
      have hnil := List.argmin_eq_none.mp hs
      have hnil' : L = [] := by simpa [graphScores] using hnil
      subst L
      simp [graphGreedy, graphScores, PairIndependent]
    | some row =>
      rcases row with ⟨v, d⟩
      have hm : (v, d) ∈ (graphScores adj L).argmin Prod.snd := by simp [hs]
      obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.argmin_mem hm)
      simp only [Prod.mk.injEq] at he
      obtain ⟨he, hed⟩ := he
      subst a
      subst d
      have hmin : ∀ a ∈ L.toFinset, pairDegree E L.toFinset v ≤ pairDegree E L.toFinset a := by
        intro a ha'
        have hrow : (a, L.countP (adj a)) ∈ graphScores adj L :=
          List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha', rfl⟩
        simpa only [graphScore_eq E adj hadj L hL] using List.le_of_mem_argmin hrow hm
      have hshort := graphPrune_shorter adj ha
      have hz := ih (graphPrune adj v L) (hL.filter _) (by omega)
      simp only [graphPrune_toFinset E adj hadj] at hz
      simpa only [graphGreedy, hs, List.toFinset_cons] using
        pair_greedy_step E L.toFinset v (List.mem_toFinset.mpr ha) hmin _ hz.1 hz.2.1 hz.2.2

/-- A bound on all counted scans, including early termination and the base case. -/
theorem graphGreedy_cost (adj : G → G → Bool) (m fuel : ℕ)
    (L : List G) (hL : L.length ≤ m) :
    (graphGreedy adj fuel L).2 ≤ fuel * (m * m + 3 * m + 1) + 1 := by
  induction fuel generalizing L with
  | zero => simp [graphGreedy]
  | succ fuel ih =>
    cases hs : (graphScores adj L).argmin Prod.snd with
    | none => simp [graphGreedy, hs]
    | some row =>
      rcases row with ⟨v, d⟩
      have hnext : (graphPrune adj v L).length ≤ m := (List.length_filter_le _ _).trans hL
      have hi := ih _ hnext
      have hsq := Nat.mul_le_mul hL hL
      simp only [graphGreedy, hs]
      change _ ≤ (fuel + 1) * (m * m + 3 * m + 1) + 1
      rw [Nat.add_mul, one_mul]
      omega

/-- The concrete algorithm reaches the independent-set threshold used in the
    binary lower bound, with at most cubic scan work in the number of vertices. -/
theorem graphGreedy_threshold (E : Finset (Finset G)) (adj : G → G → Bool)
    (hadj : ∀ a b, adj a b = true ↔ a ≠ b ∧ ({a, b} : Finset G) ∈ E)
    (L : List G) (hL : L.Nodup)
    (hE : ∀ e ∈ E, e ⊆ L.toFinset ∧ e.card = 2) {z : ℕ}
    (hstrict : (z : ℝ) * ((L.toFinset.card : ℝ) + 2 * (E.card : ℝ)) <
      (L.toFinset.card : ℝ) ^ 2) :
    let out := graphGreedy adj L.length L
    out.1.toFinset ⊆ L.toFinset ∧ PairIndependent E out.1.toFinset ∧
      z + 1 ≤ out.1.toFinset.card ∧ out.2 ≤ (L.length + 1) ^ 3 := by
  have hs := graphGreedy_spec E adj hadj L.length L hL le_rfl
  have hc := graphGreedy_cost adj L.length L.length L le_rfl
  refine ⟨hs.1, hs.2.1, card_ge_of_pair_weight E L.toFinset hE hstrict _ hs.2.2, ?_⟩
  exact hc.trans (by nlinarith)

end BinaryRuntime

end OnlineMMS
