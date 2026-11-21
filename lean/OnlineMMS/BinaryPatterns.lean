import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.Eval

namespace OnlineMMS

abbrev ApprovalPattern := Finset (Fin 5)

/-- Members of this family do not properly contain each other. -/
def IsApprovalAntichain (F : Finset ApprovalPattern) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → ¬ X ⊆ Y

private abbrev Mask := Fin 32

private def approves (i : Fin 5) (a : Mask) : Bool := a.val.testBit i.val

private def maskPattern (a : Mask) : ApprovalPattern :=
  (List.finRange 5).toFinset.filter (fun i => approves i a)

private theorem mem_maskPattern (a : Mask) (i : Fin 5) :
    i ∈ maskPattern a ↔ approves i a = true := by
  simp [maskPattern]

private theorem maskPattern_surjective : ∀ p : ApprovalPattern, ∃ a : Mask, maskPattern a = p := by
  decide +kernel

private theorem mask_and_subset :
    ∀ a b : Mask, ((a.val &&& b.val) = a.val) → maskPattern a ⊆ maskPattern b := by
  intro a b hab i hi
  have he := congrArg (fun n : ℕ => n.testBit i.val) hab
  change (a.val &&& b.val).testBit i.val = a.val.testBit i.val at he
  rw [Nat.testBit_and] at he
  have ha := (mem_maskPattern a i).mp hi
  change a.val.testBit i.val = true at ha
  simp [ha] at he
  exact (mem_maskPattern b i).mpr he

private def count (L : List Mask) (i : Fin 5) : ℕ := (L.filter (approves i)).length

private def balanced (L C : List Mask) : Bool :=
  (List.finRange 5).all fun i => decide (count C i ≤ (count L i + 1) / 2)

/-- Each bit chooses a position in the list of patterns, starting at its head. -/
private def choosePositions : List Mask → ℕ → List Mask
  | [], _ => []
  | a :: L, n =>
    let chosen := choosePositions L (n / 2)
    if n % 2 = 1 then a :: chosen else chosen

private theorem choosePositions_sublist (L : List Mask) (n : ℕ) :
    (choosePositions L n).Sublist L := by
  induction L generalizing n with
  | nil => rfl
  | cons a L ih =>
    simp only [choosePositions]
    split
    · exact (ih _).cons_cons a
    · exact (ih _).cons a

/-- Candidate position masks for the descending list of five-bit patterns.
The catalogue checks the size and all five inequalities for the chosen positions. -/
private def choices : ℕ → List ℕ
  | 0 | 1 => [0]
  | 2 | 3 => [1]
  | 4 => [6, 9, 5, 12, 10]
  | 5 => [6, 5, 9]
  | 6 => [37, 22, 35, 14, 25]
  | 7 => [38, 69, 97]
  | 8 => [54, 86, 60, 225]
  | 9 => [291]
  | 10 => [425]
  | _ => []

private def checkFamily (L : List Mask) : Bool :=
  (choices L.length).any fun n =>
    let C := choosePositions L n
    (C.length == L.length / 2) && balanced L C

private def compatible (L : List Mask) (a : Mask) : Bool :=
  L.all fun b => decide ((a.val &&& b.val) ≠ a.val ∧ (b.val &&& a.val) ≠ b.val)

private def checkCatalogue : List Mask → List Mask → Bool
  | [], built => checkFamily built
  | a :: rest, built =>
      checkCatalogue rest built && (!compatible built a || checkCatalogue rest (a :: built))

private def family (L : List Mask) : Finset ApprovalPattern := (L.map maskPattern).toFinset

private theorem mem_family (L : List Mask) (P : ApprovalPattern) :
    P ∈ family L ↔ ∃ a ∈ L, maskPattern a = P := by
  simp [family]

private theorem family_cons (a : Mask) (L : List Mask) :
    family (a :: L) = insert (maskPattern a) (family L) := by
  simp [family]

private theorem card_family (L : List Mask) (hL : (L.map maskPattern).Nodup) :
    (family L).card = L.length := by
  rw [family, List.toFinset_card_of_nodup hL, List.length_map]

private theorem card_family_filter (L : List Mask) (hL : (L.map maskPattern).Nodup) (i : Fin 5) :
    ((family L).filter (i ∈ ·)).card = count L i := by
  have hf : (family L).filter (i ∈ ·) = family (L.filter (approves i)) := by
    ext P
    simp only [Finset.mem_filter, mem_family, List.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hi⟩
      exact ⟨a, ⟨ha, (mem_maskPattern a i).mp hi⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hi⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, (mem_maskPattern a i).mpr hi⟩
  have hn : ((L.filter (approves i)).map maskPattern).Nodup :=
    (List.filter_sublist.map _).nodup hL
  rw [hf, card_family _ hn]
  rfl

private theorem checkFamily_sound {L : List Mask} (hL : (L.map maskPattern).Nodup)
    (h : checkFamily L = true) :
    ∃ C ⊆ family L, C.card = (family L).card / 2 ∧
      ∀ i : Fin 5, (C.filter (i ∈ ·)).card ≤ (((family L).filter (i ∈ ·)).card + 1) / 2 := by
  simp only [checkFamily, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨n, _, hlen, hbal⟩ := h
  let C := choosePositions L n
  have hsub : C.Sublist L := choosePositions_sublist L n
  have hCN := (hsub.map maskPattern).nodup hL
  refine ⟨family C, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨a, ha, he⟩ := (mem_family C P).mp hP
    exact (mem_family L P).mpr ⟨a, hsub.subset ha, he⟩
  · rw [card_family C hCN, card_family L hL]
    exact hlen
  · intro i
    rw [card_family_filter C hCN, card_family_filter L hL]
    simp only [balanced, List.all_eq_true, decide_eq_true_eq] at hbal
    exact hbal i (by simp)

private theorem checkCatalogue_sound (rest built : List Mask) (target : Finset ApprovalPattern)
    (hanti : IsApprovalAntichain target)
    (hnodup : (built.map maskPattern).Nodup)
    (hsub : family built ⊆ target)
    (hcover : ∀ P ∈ target, P ∈ family built ∨ P ∈ family rest)
    (hcheck : checkCatalogue rest built = true) :
    ∃ C ⊆ target, C.card = target.card / 2 ∧
      ∀ i : Fin 5, (C.filter (i ∈ ·)).card ≤ ((target.filter (i ∈ ·)).card + 1) / 2 := by
  induction rest generalizing built with
  | nil =>
    have hEq : family built = target := Finset.Subset.antisymm hsub (by
      intro P hP
      rcases hcover P hP with h | h
      · exact h
      · simp [family] at h)
    rw [← hEq]
    exact checkFamily_sound hnodup hcheck
  | cons a rest ih =>
    simp only [checkCatalogue, Bool.and_eq_true] at hcheck
    by_cases ha : maskPattern a ∈ target ∧ maskPattern a ∉ family built
    · have hcomp : compatible built a = true := by
        simp only [compatible, List.all_eq_true, decide_eq_true_eq]
        intro b hb
        have hmem : maskPattern b ∈ family built := (mem_family built _).mpr ⟨b, hb, rfl⟩
        have hba : maskPattern b ≠ maskPattern a := fun h => ha.2 (h ▸ hmem)
        exact ⟨fun h => hanti _ ha.1 _ (hsub hmem) hba.symm (mask_and_subset a b h),
          fun h => hanti _ (hsub hmem) _ ha.1 hba (mask_and_subset b a h)⟩
      apply ih (a :: built)
      · simpa [family, List.nodup_cons] using (show
          maskPattern a ∉ family built ∧ (built.map maskPattern).Nodup from ⟨ha.2, hnodup⟩)
      · rw [family_cons]
        exact Finset.insert_subset ha.1 hsub
      · intro P hP
        rw [family_cons]
        rcases hcover P hP with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · rw [family_cons] at h
          rcases Finset.mem_insert.mp h with rfl | h
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr h
      · simpa [hcomp] using hcheck.2
    · apply ih built hnodup hsub _ hcheck.1
      intro P hP
      rcases hcover P hP with h | h
      · exact Or.inl h
      · rw [family_cons] at h
        rcases Finset.mem_insert.mp h with rfl | h
        · by_cases hin : maskPattern a ∈ family built
          · exact Or.inl hin
          · exact (ha ⟨hP, hin⟩).elim
        · exact Or.inr h

/-- The possible partial antichains after scanning a prefix. -/
private def prefixes : List Mask → List Mask → List (List Mask)
  | [], built => [built]
  | a :: rest, built =>
    prefixes rest built ++ (if compatible built a then prefixes rest (a :: built) else [])

private theorem checkCatalogue_append (first last built : List Mask) :
    checkCatalogue (first ++ last) built = (prefixes first built).all (checkCatalogue last) := by
  induction first generalizing built with
  | nil => simp [prefixes]
  | cons a rest ih =>
    cases ha : compatible built a <;> simp [checkCatalogue, prefixes, ih, ha]

private theorem all_cons {α : Type} {a : α} {L : List α} {f : α → Bool}
    (ha : f a = true) (hL : L.all f = true) : (a :: L).all f = true := by simp [ha, hL]

private def prefixCases := prefixes ((List.finRange 32).take 16) []
private def suffixMasks := (List.finRange 32).drop 16

set_option maxHeartbeats 2000000 in
/-- Each of the 168 antichains on masks below 16 starts a separate kernel check.
The prefix equation verifies the literal starting lists emitted by `eval%`. -/
private theorem checkCatalogue_all :
    checkCatalogue (List.finRange 32) [] = true := by
  have hprefix : prefixCases = (eval% prefixCases) := by decide +kernel
  rw [← List.take_append_drop 16 (List.finRange 32), checkCatalogue_append]
  change prefixCases.all (checkCatalogue suffixMasks) = true
  rw [hprefix]
  iterate 168 (refine all_cons (by decide +kernel) ?_)
  rfl

/-- Every antichain of approval patterns on five coordinates admits the
balanced half-selection. The Boolean catalogue only branches on
compatible extensions, and coverage is proved for every antichain. -/
theorem five_approval_coordinates (F : Finset ApprovalPattern)
    (hanti : IsApprovalAntichain F) :
    ∃ C ⊆ F, C.card = F.card / 2 ∧
      ∀ i : Fin 5, (C.filter (i ∈ ·)).card ≤ ((F.filter (i ∈ ·)).card + 1) / 2 :=
  checkCatalogue_sound (List.finRange 32) [] F hanti List.nodup_nil (Finset.empty_subset _)
    (fun P _ => Or.inr <| (mem_family _ P).mpr <|
      let ⟨a, ha⟩ := maskPattern_surjective P
      ⟨a, by simp, ha⟩) checkCatalogue_all

end OnlineMMS
