import OnlineMMS.TwoTypePacketExecution
import OnlineMMS.TwoTypePacketRemainder

namespace OnlineMMS.TwoType

def unitPackets {m : ℕ} (P : List (Packet m)) : List (Packet m) :=
  P.filter (fun p => decide (p.level = .unit))

/-- Completed units in their current order. When there are only r−1 units,
the last candidate consists of all goods outside those units. -/
def packetMenu {m : ℕ} (R : Finset (Fin m)) (r : ℕ) (P : List (Packet m)) :
    List (Finset (Fin m)) :=
  let units := unitPackets P
  if r ≤ units.length then (units.take r).map Packet.goods
  else units.map Packet.goods ++ [R \ packetGoods units.toFinset]

/-- The exact menu of the paper satisfies the score and reserve conditions. -/
theorem packetMenu_spec {m r : ℕ} {w : Fin m → ℝ} {P : List (Packet m)}
    {R : Finset (Fin m)} (hn : P.Nodup) (hv : ValidPackets w P.toFinset)
    (ht : PacketsTerminal P.toFinset) (hsub : packetGoods P.toFinset ⊆ R)
    (hcover : bundleValue w (packetGoods P.toFinset) = bundleValue w R)
    (hR : (r : ℝ) ≤ bundleValue w R) :
    let B := packetMenu R r P
    B.length = r ∧ B.Pairwise Disjoint ∧ ∀ G ∈ B,
      G ⊆ R ∧ 1 ≤ bundleValue w G ∧ (r : ℝ) - 1 ≤ bundleValue w (R \ G) := by
  classical
  let U := unitPackets P
  have hUn : U.Nodup := hn.filter _
  have hUf : U.toFinset = P.toFinset.filter (fun p => p.level = .unit) := by
    ext p
    simp [U, unitPackets]
  have hUsub : U.toFinset ⊆ P.toFinset := by
    rw [hUf]
    exact Finset.filter_subset _ _
  have hGoodMem (p : Packet m) (hp : p ∈ U) : p.goods ⊆ R := by
    intro g hg
    apply hsub
    exact Finset.mem_biUnion.mpr ⟨p, hUsub (List.mem_toFinset.mpr hp), hg⟩
  have hUnit (p : Packet m) (hp : p ∈ U) : bundleValue w p.goods = 1 := by
    have hm : p ∈ U.toFinset := List.mem_toFinset.mpr hp
    have he : p.level = .unit := by rw [hUf] at hm; exact (Finset.mem_filter.mp hm).2
    rw [hv.weight p (hUsub hm), he]
    rfl
  have hUg : packetGoods U.toFinset ⊆ R := by
    intro g hg
    obtain ⟨p, hp, hg⟩ := Finset.mem_biUnion.mp hg
    exact hGoodMem p (List.mem_toFinset.mp hp) hg
  have hUmass : bundleValue w (packetGoods U.toFinset) = (U.length : ℝ) := by
    have hUv : ValidPackets w U.toFinset :=
      ⟨fun p hp => hv.nonempty p (hUsub hp),
       fun p hp => hv.weight p (hUsub hp),
       fun p hp q hq => hv.separate p (hUsub hp) q (hUsub hq)⟩
    rw [validPackets_mass hUv, ← List.toFinset_card_of_nodup hUn]
    calc
      _ = ∑ _p ∈ U.toFinset, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← hv.weight p (hUsub hp), hUnit p (List.mem_toFinset.mp hp)]
      _ = _ := by simp
  have hNum : r ≤ U.length + 1 := by
    have hnorm := (validPackets_mass hv).symm.trans hcover
    rw [← Finset.sum_filter_add_sum_filter_not P.toFinset (fun p => p.level = .unit)
      (fun p => p.level.weight), ← hUf, ← validPackets_mass
        (show ValidPackets w U.toFinset from
          ⟨fun p hp => hv.nonempty p (hUsub hp),
           fun p hp => hv.weight p (hUsub hp),
           fun p hp q hq => hv.separate p (hUsub hp) q (hUsub hq)⟩), hUmass] at hnorm
    have hlt := terminal_nonunit_mass_lt_two ht
    have hrlt : (r : ℝ) < (U.length : ℝ) + 2 := by linarith
    exact Nat.le_of_lt_succ (by exact_mod_cast hrlt)
  have hpair : (U.map Packet.goods).Pairwise Disjoint := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {p q} hp hq hpq =>
      hv.separate p (hUsub (List.mem_toFinset.mpr hp)) q
        (hUsub (List.mem_toFinset.mpr hq)) hpq) hUn
  have hpayU (G : Finset (Fin m)) (hG : G ∈ U.map Packet.goods) :
      G ⊆ R ∧ 1 ≤ bundleValue w G ∧ (r : ℝ) - 1 ≤ bundleValue w (R \ G) := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hG
    have hsplit := Finset.sum_sdiff (f := w) (hGoodMem p hp)
    change bundleValue w (R \ p.goods) + bundleValue w p.goods = bundleValue w R at hsplit
    refine ⟨hGoodMem p hp, (hUnit p hp).ge, ?_⟩
    linarith [hUnit p hp]
  let good (B : List (Finset (Fin m))) := B.length = r ∧ B.Pairwise Disjoint ∧ ∀ G ∈ B,
    G ⊆ R ∧ 1 ≤ bundleValue w G ∧ (r : ℝ) - 1 ≤ bundleValue w (R \ G)
  change good (if r ≤ U.length then (U.take r).map Packet.goods
    else U.map Packet.goods ++ [R \ packetGoods U.toFinset])
  by_cases hr : r ≤ U.length
  · rw [if_pos hr]
    refine ⟨by simp [List.length_take, min_eq_left hr], ?_, ?_⟩
    · exact hpair.sublist ((List.take_sublist r U).map _)
    · intro G hG
      exact hpayU G (((List.take_sublist r U).map Packet.goods).subset hG)
  · rw [if_neg hr]
    have hlength : U.length + 1 = r := by omega
    have hcast : (U.length : ℝ) + 1 = r := by exact_mod_cast hlength
    refine ⟨by simp [hlength], ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hpair, by simp, ?_⟩
      intro G hG H hH
      rw [List.mem_singleton] at hH
      subst H
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hG
      apply Finset.disjoint_left.mpr
      intro g hg hgr
      exact (Finset.mem_sdiff.mp hgr).2 (Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp, hg⟩)
    · intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact hpayU G hG
      · rw [List.mem_singleton] at hG
        subst G
        have he := Finset.sum_sdiff (f := w) hUg
        change bundleValue w (R \ packetGoods U.toFinset) + bundleValue w (packetGoods U.toFinset) =
          bundleValue w R at he
        refine ⟨Finset.sdiff_subset, by linarith, ?_⟩
        rw [Finset.sdiff_sdiff_eq_self hUg]
        linarith

end OnlineMMS.TwoType
