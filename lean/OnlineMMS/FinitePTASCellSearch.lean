import OnlineMMS.FinitePTASOnlineTwo
import Mathlib.Data.List.Sublists

namespace OnlineMMS

open scoped BigOperators

/-- Candidate bundles on the constant-size compressed instance. -/
def cellBundleCandidates (c : ℕ) : List (Finset (Fin c)) :=
  (List.finRange c).sublists.map List.toFinset

theorem cellBundleCandidates_length (c : ℕ) : (cellBundleCandidates c).length = 2^c := by
  simp [cellBundleCandidates,List.length_sublists]

/-- Stream the subsets of the available cells, stopping at the first successful test. -/
private def scanCellSubsets {c : ℕ} {α : Type} (test : Finset (Fin c) → Option α) :
    List (Fin c) → Finset (Fin c) → Option α
  | [], S => test S
  | g :: gs, S =>
    match scanCellSubsets test gs S with
    | some w => some w
    | none => scanCellSubsets test gs (insert g S)

private theorem scanCellSubsets_some {c : ℕ} {α : Type} (test : Finset (Fin c) → Option α)
    (L : List (Fin c)) (S : Finset (Fin c)) (w : α)
    (h : scanCellSubsets test L S = some w) :
    ∃ B, test B = some w := by
  induction L generalizing S with
  | nil => exact ⟨S,h⟩
  | cons x xs ih =>
    rw [scanCellSubsets] at h
    cases hleft : scanCellSubsets test xs S with
    | none =>
      rw [hleft] at h
      exact ih _ h
    | some w' =>
      rw [hleft] at h
      have he : w' = w := Option.some.inj h
      exact ih S (he ▸ hleft)

private theorem scanCellSubsets_none {c : ℕ} {α : Type} (test : Finset (Fin c) → Option α)
    (L : List (Fin c)) (S B : Finset (Fin c)) (hS : S ⊆ B) (hB : B ⊆ S ∪ L.toFinset)
    (h : scanCellSubsets test L S = none) : test B = none := by
  induction L generalizing S with
  | nil =>
    have hb : B ⊆ S := by simpa using hB
    have he : S = B := le_antisymm (show S ≤ B from hS) (show B ≤ S from hb)
    subst B
    exact h
  | cons x xs ih =>
    rw [scanCellSubsets] at h
    cases hleft : scanCellSubsets test xs S with
    | some w => simp [hleft] at h
    | none =>
      by_cases hx : x ∈ B
      · rw [hleft] at h
        apply ih (insert x S) ?_ ?_ h
        · exact Finset.insert_subset hx hS
        · intro y hy
          have hm := hB hy
          simp only [Finset.mem_union,List.toFinset_cons,Finset.mem_insert] at hm ⊢
          tauto
      · apply ih S hS ?_ hleft
        intro y hy
        have hm := hB hy
        simp only [Finset.mem_union,List.toFinset_cons,Finset.mem_insert] at hm ⊢
        have hne : y ≠ x := fun e => hx (e ▸ hy)
        tauto

private def orderedAvailableCells {c : ℕ} (v : Fin c → ℚ) (R : Finset (Fin c)) :
    List (Fin c) :=
  let cells := (List.finRange c).filter (fun g => decide (g ∈ R))
  cells.filter (fun g => decide (v g = 0)) ++ cells.filter (fun g => decide (v g ≠ 0))

private theorem orderedAvailableCells_toFinset {c : ℕ} (v : Fin c → ℚ) (R : Finset (Fin c)) :
    (orderedAvailableCells v R).toFinset = R := by
  ext g
  simp only [orderedAvailableCells,List.mem_toFinset,List.mem_append,List.mem_filter,
    decide_eq_true_eq,List.mem_finRange,true_and]
  tauto

private def tryCellBundle {c r : ℕ} (v : Fin c → ℚ) (q : ℚ) (R G : Finset (Fin c))
    (next : Finset (Fin c) → Option (Policy c 2 r)) :
    Option (Finset (Fin c) × Policy c 2 r) :=
  if G ⊆ R ∧ q ≤ rationalBundleValue v G then
    (next (R \ G)).map (fun p => (G,p))
  else none

/-- Find the first admissible bundle with a successful continuation. -/
def searchCellBundle {c r : ℕ} (v : Fin c → ℚ) (q : ℚ) (R : Finset (Fin c))
    (next : Finset (Fin c) → Option (Policy c 2 r)) :
    Option (Finset (Fin c) × Policy c 2 r) :=
  scanCellSubsets (fun G => tryCellBundle v q R G next)
    (orderedAvailableCells v R) ∅

theorem searchCellBundle_sound {c r : ℕ} (v : Fin c → ℚ) (q : ℚ) (R G : Finset (Fin c))
    (next : Finset (Fin c) → Option (Policy c 2 r)) (p : Policy c 2 r)
    (h : searchCellBundle v q R next = some (G,p)) :
    G ⊆ R ∧ (q : ℝ) ≤ bundleValue (fun g => (v g : ℝ)) G ∧
      next (R \ G) = some p := by
  obtain ⟨B,hB⟩ := scanCellSubsets_some (fun G => tryCellBundle v q R G next) _ _ _ h
  by_cases hb : B ⊆ R ∧ q ≤ rationalBundleValue v B
  · rw [tryCellBundle,if_pos hb] at hB
    cases he : next (R \ B) with
    | none => simp [he] at hB
    | some z =>
      simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hB
      obtain ⟨rfl,rfl⟩ := hB
      refine ⟨hb.1,?_,he⟩
      rw [← rationalBundleValue_cast]
      exact_mod_cast hb.2
  · simp [tryCellBundle,hb] at hB

theorem searchCellBundle_complete {c r : ℕ} (v : Fin c → ℚ) (q : ℚ) (R G : Finset (Fin c))
    (next : Finset (Fin c) → Option (Policy c 2 r)) (p : Policy c 2 r)
    (hs : G ⊆ R) (hq : (q : ℝ) ≤ bundleValue (fun g => (v g : ℝ)) G)
    (hp : next (R \ G) = some p) :
    ∃ res, searchCellBundle v q R next = some res := by
  have hr : q ≤ rationalBundleValue v G := by
    rw [← rationalBundleValue_cast] at hq
    exact_mod_cast hq
  cases he : searchCellBundle v q R next with
  | some res => exact ⟨res,rfl⟩
  | none =>
    have hG : G ⊆ ∅ ∪ (orderedAvailableCells v R).toFinset := by
      simpa [orderedAvailableCells_toFinset] using hs
    have hz := scanCellSubsets_none (fun G => tryCellBundle v q R G next) _ ∅ G
      (Finset.empty_subset _) hG he
    simp [tryCellBundle,hs,hr,hp] at hz

/-- Search on a constant number of representative cells. Both child policies
must succeed before returning a policy at a nonterminal node. -/
def searchCellPolicy {c : ℕ} (v : Fin 2 → Fin c → ℚ) (q : Fin 2 → ℚ) :
    (r : ℕ) → Finset (Fin c) → Option (Policy c 2 r)
  | 0, _ => some .done
  | r+1, R => do
    let F := fun t => searchCellBundle (v t) (q t) R (searchCellPolicy v q r)
    let a ← F 0
    let b ← F 1
    pure (.step (fun t => if t = 0 then a.1 else b.1)
      (fun t => if t = 0 then a.2 else b.2))

theorem searchCellPolicy_sound {c r : ℕ} (v : Fin 2 → Fin c → ℚ) (q : Fin 2 → ℚ)
    (R : Finset (Fin c)) (p : Policy c 2 r) (h : searchCellPolicy v q r R = some p) :
    p.Guarantees (fun t g => (v t g : ℝ)) (fun t => (q t : ℝ)) R := by
  induction r generalizing R with
  | zero => cases p; trivial
  | succ r ih =>
    let F := fun t => searchCellBundle (v t) (q t) R (searchCellPolicy v q r)
    change (do
      let a ← F 0
      let b ← F 1
      pure (.step (fun t => if t = 0 then a.1 else b.1)
        (fun t => if t = 0 then a.2 else b.2))) = some p at h
    cases ha : F 0 with
    | none => simp [ha] at h
    | some a =>
      cases hb : F 1 with
      | none => simp [ha,hb] at h
      | some b =>
        rw [ha,hb] at h
        change some (.step (fun t => if t = 0 then a.1 else b.1)
          (fun t => if t = 0 then a.2 else b.2)) = some p at h
        injection h with hh
        subst p
        have h0 := searchCellBundle_sound _ _ _ _ _ _ ha
        have h1 := searchCellBundle_sound _ _ _ _ _ _ hb
        intro t
        rcases shortType_cases 0 t with he | he
        · subst t
          simpa using ⟨h0.1,h0.2.1,ih _ _ h0.2.2⟩
        · have he' : t = 1 := he
          subst t
          simpa using ⟨h1.1,h1.2.1,ih _ _ h1.2.2⟩

theorem searchCellPolicy_complete {c r : ℕ} (v : Fin 2 → Fin c → ℚ) (q : Fin 2 → ℚ)
    (R : Finset (Fin c)) (p : Policy c 2 r)
    (h : p.Guarantees (fun t g => (v t g : ℝ)) (fun t => (q t : ℝ)) R) :
    ∃ p', searchCellPolicy v q r R = some p' := by
  induction r generalizing R with
  | zero => exact ⟨.done,rfl⟩
  | succ r ih =>
    cases p with
    | step G sub =>
      have all (t : Fin 2) := h t
      have suc (t : Fin 2) : ∃ x, searchCellBundle (v t) (q t) R
          (searchCellPolicy v q r) = some x := by
        obtain ⟨p',hp'⟩ := ih _ _ (all t).2.2
        exact searchCellBundle_complete _ _ _ _ _ _ (all t).1 (all t).2.1 hp'
      obtain ⟨a,ha⟩ := suc 0
      obtain ⟨b,hb⟩ := suc 1
      refine ⟨.step (fun t => if t = 0 then a.1 else b.1)
        (fun t => if t = 0 then a.2 else b.2),?_⟩
      simp [searchCellPolicy,ha,hb]

/-- A bound on search-node visits when every bundle is tested. -/
def cellPolicySearchCalls (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => 1 + 2*2^c * cellPolicySearchCalls c r

theorem cellPolicySearchCalls_mono {c d : ℕ} (h : c ≤ d) (r : ℕ) :
    cellPolicySearchCalls c r ≤ cellPolicySearchCalls d r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [cellPolicySearchCalls]
    exact Nat.add_le_add_left (Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) h)) ih) 1

theorem cellPolicySearchCalls_short {c r : ℕ} (hc : c ≤ 25) (hr : r ≤ 5) :
    cellPolicySearchCalls c r ≤ cellPolicySearchCalls 25 5 := by
  apply (cellPolicySearchCalls_mono hc r).trans
  apply monotone_nat_of_le_succ _ hr
  intro i
  simp only [cellPolicySearchCalls]
  exact (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_add_left _ _)

end OnlineMMS
