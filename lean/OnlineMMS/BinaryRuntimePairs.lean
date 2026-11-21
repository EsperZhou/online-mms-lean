import OnlineMMS.BinarySupport

namespace OnlineMMS.BinaryRuntime

variable {G : Type*} [DecidableEq G]

/-- Turn the first twice `c` items in a row into adjacent pairs. -/
def rowPairs : ℕ → List G → List (Finset G)
  | c + 1, a :: b :: rest => {a, b} :: rowPairs c rest
  | _, _ => []

theorem rowPairs_subset (c : ℕ) (L : List G) {e : Finset G} (he : e ∈ rowPairs c L) :
    e ⊆ L.toFinset := by
  induction c generalizing L with
  | zero => simp [rowPairs] at he
  | succ c ih =>
    cases L with
    | nil => simp [rowPairs] at he
    | cons a L =>
      cases L with
      | nil => simp [rowPairs] at he
      | cons b rest =>
        simp only [rowPairs, List.mem_cons] at he
        rcases he with rfl | he
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          exact List.mem_toFinset.mpr (by rcases hx with rfl | rfl <;> simp)
        · exact (ih rest he).trans (fun _ hx => List.mem_toFinset.mpr
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))))

/-- The row scan constructs exactly the designated disjoint pairs. -/
theorem rowPairs_spec (c : ℕ) (L : List G) (hL : L.Nodup) (hc : 2 * c ≤ L.length) :
    (rowPairs c L).toFinset.card = c ∧
      (↑(rowPairs c L).toFinset : Set (Finset G)).Pairwise Disjoint ∧
      ∀ e ∈ (rowPairs c L).toFinset, e ⊆ L.toFinset ∧ e.card = 2 := by
  induction c generalizing L with
  | zero => simp [rowPairs]
  | succ c ih =>
    cases L with
    | nil => simp at hc
    | cons a L =>
      cases L with
      | nil => simp at hc; omega
      | cons b rest =>
        simp only [List.nodup_cons, List.mem_cons, not_or] at hL
        obtain ⟨hc', hD, hRest⟩ := ih rest hL.2.2 (by simp at hc; omega)
        let e : Finset G := {a, b}
        have hec : e.card = 2 := Finset.card_eq_two.mpr ⟨a, b, hL.1.1, rfl⟩
        have hdisj (f : Finset G) (hf : f ∈ (rowPairs c rest).toFinset) : Disjoint e f := by
          apply Finset.disjoint_left.mpr
          intro x hx hxf
          have hxr := List.mem_toFinset.mp ((hRest f hf).1 hxf)
          simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hL.1.2 hxr
          · exact hL.2.1 hxr
        have hnot : e ∉ (rowPairs c rest).toFinset := by
          intro he
          have hz := Finset.disjoint_left.mp (hdisj e he) (show a ∈ e by simp [e])
          exact hz (by simp [e])
        simp only [rowPairs, List.toFinset_cons]
        change (insert e (rowPairs c rest).toFinset).card = c + 1 ∧ _
        rw [Finset.card_insert_of_not_mem hnot, hc']
        refine ⟨rfl, ?_, ?_⟩
        · intro f hf g hg hne
          change f ∈ insert e (rowPairs c rest).toFinset at hf
          change g ∈ insert e (rowPairs c rest).toFinset at hg
          rcases Finset.mem_insert.mp hf with rfl | hf
          · rcases Finset.mem_insert.mp hg with rfl | hg
            · exact (hne rfl).elim
            · exact hdisj _ hg
          · rcases Finset.mem_insert.mp hg with rfl | hg
            · exact (hdisj _ hf).symm
            · exact hD hf hg hne
        · intro f hf
          refine ⟨?_, ?_⟩
          · simpa only [List.toFinset_cons] using
              rowPairs_subset (c + 1) (a :: b :: rest) (by
                apply List.mem_toFinset.mp
                simpa only [rowPairs, List.toFinset_cons] using hf)
          · change f ∈ insert e (rowPairs c rest).toFinset at hf
            rcases Finset.mem_insert.mp hf with rfl | hf
            · exact hec
            · exact (hRest _ hf).2

/-- One visit per successful pair plus a terminating branch. -/
def rowPairsCost (G : Type*) : ℕ → List G → ℕ
  | c + 1, _ :: _ :: rest => 1 + rowPairsCost G c rest
  | _, _ => 1

omit [DecidableEq G] in
theorem rowPairsCost_le (c : ℕ) (L : List G) : rowPairsCost G c L ≤ c + 1 := by
  induction c generalizing L with
  | zero => simp [rowPairsCost]
  | succ c ih =>
    cases L with
    | nil => simp [rowPairsCost]
    | cons a L =>
      cases L with
      | nil => simp [rowPairsCost]
      | cons b rest =>
        have h := ih rest
        simp only [rowPairsCost]
        omega

end OnlineMMS.BinaryRuntime
