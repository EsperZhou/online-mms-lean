import OnlineMMS.TwoTypePacketPolicy

namespace OnlineMMS.TwoType

private theorem PacketMerge.keeps_unit {m : ℕ} {P Q : Finset (Packet m)} (h : PacketMerge P Q)
    {p : Packet m} (hp : p ∈ P) (hu : p.level = .unit) : p ∈ Q := by
  obtain ⟨take, src, dest, arity, _, hcarry, _, hl, rfl⟩ := h.witness
  apply Finset.mem_insert_of_mem
  refine Finset.mem_sdiff.mpr ⟨hp, ?_⟩
  intro ht
  have he := hl p ht
  rw [hu] at he
  rw [← he] at hcarry
  simp [PacketLevel.carry] at hcarry

theorem normalizePackets_keeps_unit {m : ℕ} (fuel : ℕ) {P : List (Packet m)} {w : Fin m → ℝ}
    (hn : P.Nodup) (hv : ValidPackets w P.toFinset)
    {p : Packet m} (hp : p ∈ P) (hu : p.level = .unit) :
    p ∈ (normalizePackets fuel P).1 := by
  induction fuel generalizing P with
  | zero => exact hp
  | succ fuel ih =>
    unfold normalizePackets
    cases hstep : packetStep P with
    | none => exact hp
    | some Q =>
      have hmerge := packetStep_sound hn hstep
      have hq := packetStep_nodup hn hv hstep
      have hvQ := (hmerge.valid hv).1
      have hpQ := List.mem_toFinset.mp (hmerge.keeps_unit (List.mem_toFinset.mpr hp) hu)
      simpa only [Option.some.injEq] using ih hq hvQ hpQ

/-- When the initial score equals the required number of packages, every
completed unit is offered, including each original unit singleton. -/
theorem preparedMenu_offers_unit {m r : ℕ} (tag : Fin m → Option PacketLevel)
    (R : Finset (Fin m)) (w : Fin m → ℝ) (hw : ∀ g, w g = (tag g).elim 0 PacketLevel.weight)
    (hnon : ∀ g, 0 ≤ w g) (htotal : bundleValue w R = r)
    {g : Fin m} (hg : g ∈ R) (ht : tag g = some .unit) :
    {g} ∈ preparedMenu tag R r := by
  classical
  let P := initialPackets tag R
  let Q := (normalizePackets P.length P).1
  let p : Packet m := ⟨{g}, .unit⟩
  have hpP : p ∈ P := by
    apply List.mem_filterMap.mpr
    exact ⟨g, (Finset.mem_sort _).mpr hg, by simp [ht, p]⟩
  obtain ⟨hpN, hpV, hpSub, _⟩ := initialPackets_spec tag R w hw
  have hpQ : p ∈ Q := normalizePackets_keeps_unit P.length hpN hpV hpP rfl
  have hspec := normalizePackets_spec P.length P hpN hpV le_rfl
  change Q.Nodup ∧ ValidPackets w Q.toFinset ∧ packetGoods Q.toFinset = packetGoods P.toFinset ∧ _ at hspec
  let U := unitPackets Q
  have hUn : U.Nodup := hspec.1.filter _
  have hu (q : Packet m) (hq : q ∈ U.toFinset) : q ∈ Q.toFinset ∧ q.level = .unit := by
    simpa [U, unitPackets] using hq
  have huV : ValidPackets w U.toFinset :=
    ⟨fun q hq => hspec.2.1.nonempty q (hu q hq).1,
     fun q hq => hspec.2.1.weight q (hu q hq).1,
     fun q hq t ht' => hspec.2.1.separate q (hu q hq).1 t (hu t ht').1⟩
  have huSub : packetGoods U.toFinset ⊆ R := by
    intro i hi
    obtain ⟨q, hq, hqi⟩ := Finset.mem_biUnion.mp hi
    apply hpSub
    rw [← hspec.2.2.1]
    exact Finset.mem_biUnion.mpr ⟨q, (hu q hq).1, hqi⟩
  have hsize : U.length ≤ r := by
    have hm : bundleValue w (packetGoods U.toFinset) = (U.length : ℝ) := by
      rw [validPackets_mass huV, ← List.toFinset_card_of_nodup hUn]
      calc
        _ = ∑ _q ∈ U.toFinset, (1 : ℝ) :=
          Finset.sum_congr rfl fun q hq => by rw [(hu q hq).2]; rfl
        _ = _ := by simp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := w) huSub (fun i _ _ => hnon i)
    change bundleValue w (packetGoods U.toFinset) ≤ bundleValue w R at hle
    rw [hm, htotal] at hle
    exact_mod_cast hle
  have hpU : p ∈ U := by simp [U, unitPackets, hpQ, p]
  have hpB : {g} ∈ U.map Packet.goods := List.mem_map.mpr ⟨p, hpU, rfl⟩
  change {g} ∈ if r ≤ U.length then (U.take r).map Packet.goods
    else U.map Packet.goods ++ [R \ packetGoods U.toFinset]
  split
  · rw [List.take_of_length_le hsize]
    exact hpB
  · exact List.mem_append_left _ hpB

end OnlineMMS.TwoType
