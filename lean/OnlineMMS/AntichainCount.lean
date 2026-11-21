import OnlineMMS.BinaryPatterns
import Mathlib.Data.List.Nodup
import Mathlib.SetTheory.Cardinal.Finite

namespace OnlineMMS.FiveCatalogue

private abbrev Family := Finset ApprovalPattern

private def compatible (p : ApprovalPattern) (F : Family) : Bool :=
  decide (∀ a ∈ F, ¬ a ⊆ p ∧ ¬ p ⊆ a)

/-- Enumerate all antichains from the permitted patterns. Families omitting `p` form
the first block; the second block attaches `p` to the families incomparable with it. -/
private def catalogue : List ApprovalPattern → List Family
  | [] => [∅]
  | p :: ps =>
    let tail := catalogue ps
    tail ++ (tail.filter (compatible p)).map (insert p)

private theorem anti_mono {F H : Family} (h : F ⊆ H) (ha : IsApprovalAntichain H) :
    IsApprovalAntichain F := fun x hx y hy => ha x (h hx) y (h hy)

private theorem anti_insert {F : Family} {p : ApprovalPattern} (hF : IsApprovalAntichain F)
    (hc : compatible p F = true) : IsApprovalAntichain (insert p F) := by
  simp only [compatible, decide_eq_true_eq] at hc
  intro a ha b hb hn
  by_cases hap : a = p
  · subst a
    exact (hc b ((Finset.mem_insert.mp hb).resolve_left hn.symm)).2
  · have haF := (Finset.mem_insert.mp ha).resolve_left hap
    by_cases hbp : b = p
    · subst b
      exact (hc a haF).1
    · exact hF a haF b ((Finset.mem_insert.mp hb).resolve_left hbp) hn

private theorem mem_catalogue (ps : List ApprovalPattern) (F : Family) :
    F ∈ catalogue ps ↔ (F ⊆ ps.toFinset ∧ IsApprovalAntichain F) := by
  induction ps generalizing F with
  | nil =>
    simp [catalogue, IsApprovalAntichain, Finset.subset_empty]
    rintro rfl
    simp
  | cons p ps ih =>
    rw [catalogue, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨A,ha,rfl⟩)
      · exact ⟨(ih _ |>.mp h).1.trans (by simp), (ih _ |>.mp h).2⟩
      · obtain ⟨ha, hc⟩ := List.mem_filter.mp ha
        obtain ⟨hs, han⟩ := (ih _).mp ha
        exact ⟨by simpa using Finset.insert_subset_insert p hs, anti_insert han hc⟩
    · rintro ⟨hs, ha⟩
      by_cases hp : p ∈ F
      · apply Or.inr
        refine ⟨F.erase p, List.mem_filter.mpr ⟨(ih _).2 ⟨?_, anti_mono (Finset.erase_subset ..) ha⟩, ?_⟩,
          Finset.insert_erase hp⟩
        · intro a hmem
          have h := hs (Finset.mem_of_mem_erase hmem)
          simpa [List.toFinset_cons, (Finset.mem_erase.mp hmem).1] using h
        · simp only [compatible, decide_eq_true_eq]
          intro a hmem
          obtain ⟨hneq, hF⟩ := Finset.mem_erase.mp hmem
          exact ⟨ha a hF p hp hneq, ha p hp a hF hneq.symm⟩
      · apply Or.inl
        apply (ih _).2
        refine ⟨?_, ha⟩
        intro a hmem
        have hneq : a ≠ p := fun eq => hp (eq ▸ hmem)
        simpa [List.toFinset_cons, hneq] using hs hmem

private theorem nodup_catalogue (ps : List ApprovalPattern) (hps : ps.Nodup) :
    (catalogue ps).Nodup := by
  induction ps with
  | nil => simp [catalogue]
  | cons p ps ih =>
    obtain ⟨hp, hps⟩ := List.nodup_cons.mp hps
    have absent {F : Family} (hf : F ∈ catalogue ps) : p ∉ F := by
      intro hpf
      exact hp (List.mem_toFinset.mp (((mem_catalogue ps F).mp hf).1 hpf))
    rw [catalogue, List.nodup_append]
    refine ⟨ih hps, ?_, ?_⟩
    · apply List.Nodup.map_on _ ((ih hps).filter _)
      intro A ha B hb he
      have hA := absent (List.mem_filter.mp ha).1
      have hB := absent (List.mem_filter.mp hb).1
      simpa [Finset.erase_insert hA, Finset.erase_insert hB] using congrArg (fun F : Family => F.erase p) he
    · intro A hA hA'
      obtain ⟨B, _, rfl⟩ := List.mem_map.mp hA'
      exact absent hA (Finset.mem_insert_self p B)

private def allPatterns : List ApprovalPattern := (List.finRange 5).sublists.map List.toFinset

private theorem allPatterns_nodup : allPatterns.Nodup := by decide +kernel
private theorem allPatterns_complete : ∀ p : ApprovalPattern, p ∈ allPatterns := by decide +kernel

/-- The index of a pattern is its five-bit characteristic vector. -/
private def patternIndex (p : ApprovalPattern) : ℕ :=
  (List.finRange 5).foldr (fun i n => 2 * n + (decide (i ∈ p)).toNat) 0

/-- Bit `b` is set exactly when pattern `b` is incomparable with pattern `a`. -/
private def incomparableBits (a : ℕ) : ℕ :=
  (List.range 32).foldr
    (fun b n => 2 * n + ((a &&& b != a) && (a &&& b != b)).toNat) 0

private theorem incomparableBits_spec : ∀ p q : ApprovalPattern,
    (incomparableBits (patternIndex p)).testBit (patternIndex q) = true ↔ ¬ q ⊆ p ∧ ¬ p ⊆ q := by
  decide +kernel

private def row (p : ApprovalPattern) : ℕ × ℕ :=
  (patternIndex p, incomparableBits (patternIndex p))

/-- Omit the current pattern or include it and restrict the remaining choices. -/
private def countAvailable : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 1
  | (i, m) :: rs, available =>
      if available.testBit i then
        countAvailable rs available + countAvailable rs (available &&& m)
      else countAvailable rs available

private def permitted (available : ℕ) (F : Family) : Bool :=
  decide (∀ q ∈ F, available.testBit (patternIndex q) = true)

private theorem countAvailable_eq (ps : List ApprovalPattern) (available : ℕ) :
    countAvailable (ps.map row) available = (catalogue ps).countP (permitted available) := by
  induction ps generalizing available with
  | nil => simp [countAvailable, catalogue, permitted]
  | cons p ps ih =>
    simp only [List.map_cons, row, countAvailable, catalogue, List.countP_append, List.countP_map,
      List.countP_filter, Function.comp_apply]
    split <;> rename_i hp
    · rw [ih, ih]
      congr 1
      apply List.countP_congr
      intro F _
      simp [permitted, compatible, Nat.testBit_and, incomparableBits_spec, hp, forall_and]
    · rw [ih]
      have hz : (fun F => permitted available (insert p F) && compatible p F) = fun _ => false := by
        funext F
        simp [permitted, hp]
      rw [hz]
      simp

private theorem catalogue_length : (catalogue allPatterns).length = 7581 := by
  let allBits := 2 ^ 32 - 1
  have hbits : ∀ p : ApprovalPattern, allBits.testBit (patternIndex p) = true := by decide +kernel
  have hall : permitted allBits = fun _ => true := by
    funext F
    simp [permitted, hbits]
  have evaluation : countAvailable (allPatterns.map row) allBits = 7581 := by decide +kernel
  simpa [countAvailable_eq, hall] using evaluation

/-- Exact number of antichains of subsets of the five approval coordinates, including
the empty family. Each antichain is represented exactly once. -/
theorem number_of_five_coordinate_antichains :
    Nat.card {F : Finset ApprovalPattern // IsApprovalAntichain F} = 7581 := by
  let E := (catalogue allPatterns).toFinset
  have hc (F : Family) : F ∈ E ↔ IsApprovalAntichain F := by
    change F ∈ (catalogue allPatterns).toFinset ↔ _
    rw [List.mem_toFinset, mem_catalogue]
    exact and_iff_right (fun p _ => List.mem_toFinset.mpr (allPatterns_complete p))
  let e : {F : Family // IsApprovalAntichain F} ≃ ↥E :=
    ⟨fun f => ⟨f.val, (hc _).mpr f.property⟩,
     fun f => ⟨f.val, (hc _).mp f.property⟩, fun _ => rfl, fun _ => rfl⟩
  calc
    _ = Nat.card (↥E) := Nat.card_congr e
    _ = E.card := by simp
    _ = (catalogue allPatterns).length := List.toFinset_card_of_nodup (nodup_catalogue _ allPatterns_nodup)
    _ = 7581 := catalogue_length

/-- The family of all pairs of coordinates attains the ten-member Sperner bound. -/
theorem ten_member_antichain_exists :
    ∃ F : Finset ApprovalPattern, IsApprovalAntichain F ∧ F.card = 10 := by
  refine ⟨(Finset.univ : Finset (Fin 5)).powersetCard 2, ?_, ?_⟩
  · intro a ha b hb hab hsub
    have ha2 := (Finset.mem_powersetCard.mp ha).2
    have hb2 := (Finset.mem_powersetCard.mp hb).2
    exact hab (Finset.eq_of_subset_of_card_le hsub (by omega))
  · rw [Finset.card_powersetCard]
    decide

/-- A terminal family with ten members has exactly 252 half-size candidates. -/
theorem ten_member_half_subfamilies {F : Finset ApprovalPattern} (h : F.card = 10) :
    (F.powersetCard (F.card / 2)).card = 252 := by
  rw [Finset.card_powersetCard, h]
  decide

end OnlineMMS.FiveCatalogue
