import OnlineMMS.TwoTypePacketMerge

namespace OnlineMMS.TwoType

private def packetStepAt {m : ℕ} (P : List (Packet m)) (src : PacketLevel) :
    Option (List (Packet m)) := do
  let (arity, dest) ← src.carry
  let group := P.filter (fun p => decide (p.level = src))
  if arity ≤ group.length then
    let take := (group.take arity).toFinset
    some (⟨packetGoods take, dest⟩ :: P.filter (fun p => decide (p ∉ take)))
  else none

/-- Lexicographic tie breaking by the current list order. Each trial scans
the current list for two or three packets of the trial level. -/
def packetStep {m : ℕ} (P : List (Packet m)) : Option (List (Packet m)) :=
  P.findSome? (fun p => packetStepAt P p.level)

private theorem packetStepAt_sound {m : ℕ} {P Q : List (Packet m)} {src : PacketLevel}
    (hn : P.Nodup) (hs : packetStepAt P src = some Q) : PacketMerge P.toFinset Q.toFinset := by
  unfold packetStepAt at hs
  cases hcarry : src.carry with
  | none => simp [hcarry] at hs
  | some data =>
    obtain ⟨arity, dest⟩ := data
    simp only [hcarry, Option.bind_some] at hs
    let group := P.filter (fun p => decide (p.level = src))
    by_cases hl : arity ≤ group.length
    · change (if arity ≤ group.length then _ else none) = some Q at hs
      rw [if_pos hl, Option.some.injEq] at hs
      let take := (group.take arity).toFinset
      have hgroup (p : Packet m) (hp : p ∈ take) : p ∈ P ∧ p.level = src := by
        have hmem := (List.take_sublist arity group).subset (List.mem_toFinset.mp hp)
        simpa [group] using hmem
      refine ⟨⟨take, src, dest, arity, fun p hp => List.mem_toFinset.mpr (hgroup p hp).1,
        hcarry, ?_, fun p hp => (hgroup p hp).2, ?_⟩⟩
      · rw [List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup (hn.filter _)),
          List.length_take, min_eq_left hl]
      · rw [← hs]
        ext p
        simp [take, group, and_comm]
    · change (if arity ≤ group.length then _ else none) = some Q at hs
      simp [hl] at hs

theorem packetStep_sound {m : ℕ} {P Q : List (Packet m)} (hn : P.Nodup)
    (hs : packetStep P = some Q) : PacketMerge P.toFinset Q.toFinset := by
  obtain ⟨_, p, _, _, hp, _⟩ := List.findSome?_eq_some_iff.mp hs
  exact packetStepAt_sound hn hp

theorem packetStep_none_terminal {m : ℕ} {P : List (Packet m)} (hn : P.Nodup)
    (hs : packetStep P = none) : PacketsTerminal P.toFinset := by
  intro Q h
  obtain ⟨take, src, dest, arity, hsub, hcarry, hcard, hlevel, _⟩ := h.witness
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hcard]; have := (PacketLevel.carry_spec hcarry).1; omega)
  have hpP := List.mem_toFinset.mp (hsub hp)
  have hnstep := List.findSome?_eq_none_iff.mp hs p hpP
  rw [hlevel p hp] at hnstep
  let group := P.filter (fun p => decide (p.level = src))
  have hlen : arity ≤ group.length := by
    rw [← hcard, ← List.toFinset_card_of_nodup (hn.filter _)]
    apply Finset.card_le_card
    intro q hq
    have hmem := List.mem_toFinset.mp (hsub hq)
    simp [group, hmem, hlevel q hq]
  simp [packetStepAt, hcarry, show arity ≤ (P.filter (fun p => decide (p.level = src))).length from hlen] at hnstep

theorem packetStep_nodup {m : ℕ} {P Q : List (Packet m)} {w : Fin m → ℝ}
    (hn : P.Nodup) (hv : ValidPackets w P.toFinset) (hs : packetStep P = some Q) :
    Q.Nodup := by
  obtain ⟨_, p, _, _, hp, _⟩ := List.findSome?_eq_some_iff.mp hs
  unfold packetStepAt at hp
  cases hcarry : p.level.carry with
  | none => simp [hcarry] at hp
  | some data =>
    obtain ⟨arity, dest⟩ := data
    let group := P.filter (fun q => decide (q.level = p.level))
    by_cases hl : arity ≤ group.length
    · simp only [hcarry, Option.bind_some] at hp
      change (if arity ≤ group.length then _ else none) = some Q at hp
      rw [if_pos hl, Option.some.injEq] at hp
      rw [← hp, List.nodup_cons]
      refine ⟨?_, hn.filter _⟩
      let take := (group.take arity).toFinset
      let merged : Packet m := ⟨packetGoods take, dest⟩
      change merged ∉ P.filter (fun q => decide (q ∉ take))
      intro hm
      have hw : merged ∈ P.toFinset ∧ merged ∉ take := by simpa using hm
      have harity := (PacketLevel.carry_spec hcarry).1
      have hcard : take.card = arity := by
        rw [List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup (hn.filter _)),
          List.length_take, min_eq_left hl]
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hcard]; omega : 0 < take.card)
      have hxP : x ∈ P.toFinset := List.mem_toFinset.mpr
        ((List.filter_sublist).subset ((List.take_sublist arity group).subset (List.mem_toFinset.mp hx)))
      have hne : x ≠ merged := fun h => hw.2 (h ▸ hx)
      obtain ⟨g, hg⟩ := hv.nonempty x hxP
      have hg' : g ∈ merged.goods := Finset.mem_biUnion.mpr ⟨x, hx, hg⟩
      exact Finset.disjoint_left.mp (hv.separate x hxP merged hw.1 hne) hg hg'
    · simp [hcarry, show ¬ arity ≤ (P.filter (fun q => decide (q.level = p.level))).length from hl] at hp

/-- Run the deterministic merging pass with enough fuel for every possible
merge. The counter records the number of successful merges. -/
def normalizePackets {m : ℕ} : ℕ → List (Packet m) → List (Packet m) × ℕ
  | 0, P => (P, 0)
  | fuel + 1, P =>
    match packetStep P with
    | none => (P, 0)
    | some Q =>
      let (R, count) := normalizePackets fuel Q
      (R, count + 1)

theorem normalizePackets_spec {m : ℕ} {w : Fin m → ℝ}
    (fuel : ℕ) (P : List (Packet m)) (hn : P.Nodup)
    (hv : ValidPackets w P.toFinset) (hfuel : P.length ≤ fuel) :
    let (Q, count) := normalizePackets fuel P
    Q.Nodup ∧ ValidPackets w Q.toFinset ∧
      packetGoods Q.toFinset = packetGoods P.toFinset ∧
      PacketsTerminal Q.toFinset ∧ count + Q.length ≤ P.length := by
  induction fuel generalizing P with
  | zero =>
    have hp : P = [] := List.length_eq_zero_iff.mp (by omega)
    subst P
    refine ⟨hn, hv, rfl, packetStep_none_terminal hn rfl, ?_⟩
    simp [normalizePackets]
  | succ fuel ih =>
    unfold normalizePackets
    cases hstep : packetStep P with
    | none => exact ⟨hn, hv, rfl, packetStep_none_terminal hn hstep, by simp⟩
    | some Q =>
      have hnormal := (packetStep_sound hn hstep).valid hv
      have hq := packetStep_nodup hn hv hstep
      have hlt := hnormal.2.2
      rw [List.toFinset_card_of_nodup hq, List.toFinset_card_of_nodup hn] at hlt
      specialize ih Q hq hnormal.1 (by omega)
      rcases hres : normalizePackets fuel Q with ⟨R, count⟩
      rw [hres] at ih
      change let (Q', count') := normalizePackets fuel Q
        Q'.Nodup ∧ ValidPackets w Q'.toFinset ∧
          packetGoods Q'.toFinset = packetGoods P.toFinset ∧
          PacketsTerminal Q'.toFinset ∧ count' + 1 + Q'.length ≤ P.length
      rw [hres]
      exact ⟨ih.1, ih.2.1, ih.2.2.1.trans hnormal.2.1, ih.2.2.2.1, by
        have := ih.2.2.2.2
        omega⟩

end OnlineMMS.TwoType
