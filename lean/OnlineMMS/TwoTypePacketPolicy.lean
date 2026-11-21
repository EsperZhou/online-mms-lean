import OnlineMMS.TwoTypePacketMenu
import OnlineMMS.TwoTypeRationalScores
import Mathlib.Data.List.MinMax

namespace OnlineMMS.TwoType

def initialPackets {m : ℕ} (tag : Fin m → Option PacketLevel) (R : Finset (Fin m)) :
    List (Packet m) :=
  (R.sort (· ≤ ·)).filterMap fun g => (tag g).map (fun lvl => ⟨{g}, lvl⟩)

private theorem mem_initialPackets {m : ℕ} {tag : Fin m → Option PacketLevel}
    {R : Finset (Fin m)} {p : Packet m} :
    p ∈ initialPackets tag R ↔ ∃ g ∈ R, tag g = some p.level ∧ p.goods = {g} := by
  constructor
  · intro hp
    obtain ⟨g, hg, h⟩ := List.mem_filterMap.mp hp
    cases he : tag g with
    | none => simp [he] at h
    | some lvl =>
      have hp' : (⟨{g}, lvl⟩ : Packet m) = p := by
        rw [he] at h
        exact Option.some.inj h
      subst p
      exact ⟨g, (Finset.mem_sort _).mp hg, he, rfl⟩
  · rintro ⟨g, hg, htag, he⟩
    apply List.mem_filterMap.mpr
    exact ⟨g, (Finset.mem_sort _).mpr hg, by simp [htag, ← he]⟩

theorem initialPackets_length {m : ℕ} (tag : Fin m → Option PacketLevel) (R : Finset (Fin m)) :
    (initialPackets tag R).length ≤ R.card := by
  unfold initialPackets
  simpa only [Finset.length_sort] using List.length_filterMap_le _ (R.sort (· ≤ ·))

theorem initialPackets_spec {m : ℕ} (tag : Fin m → Option PacketLevel) (R : Finset (Fin m))
    (w : Fin m → ℝ) (hw : ∀ g, w g = (tag g).elim 0 PacketLevel.weight) :
    let P := initialPackets tag R
    P.Nodup ∧ ValidPackets w P.toFinset ∧
      packetGoods P.toFinset ⊆ R ∧ bundleValue w (packetGoods P.toFinset) = bundleValue w R := by
  let P := initialPackets tag R
  have hp (p : Packet m) (hm : p ∈ P.toFinset) :
      ∃ g ∈ R, tag g = some p.level ∧ p.goods = {g} :=
    mem_initialPackets.mp (List.mem_toFinset.mp hm)
  have hsub : packetGoods P.toFinset ⊆ R := by
    intro g hg
    obtain ⟨p, hpP, hpg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨i, hi, _, he⟩ := hp p hpP
    simpa [he] using (Finset.mem_singleton.mp (he ▸ hpg) ▸ hi : g ∈ R)
  refine ⟨?_, ⟨?_, ?_, ?_⟩, hsub, ?_⟩
  · apply List.Nodup.filterMap _ (Finset.sort_nodup _ _)
    intro a b p ha hb
    cases haTag : tag a <;> cases hbTag : tag b <;> simp_all
    have he := congrArg Packet.goods (ha.trans hb.symm)
    simpa using he
  · intro p hpP
    obtain ⟨_, _, _, he⟩ := hp p hpP
    simp [he]
  · intro p hpP
    obtain ⟨g, _, htag, he⟩ := hp p hpP
    simp [bundleValue, he, hw g, htag]
  · intro p hpP q hqP hne
    obtain ⟨i, _, hi, hpg⟩ := hp p hpP
    obtain ⟨j, _, hj, hqg⟩ := hp q hqP
    rw [hpg, hqg, Finset.disjoint_singleton]
    intro he
    subst j
    have hlevel : p.level = q.level := Option.some.inj (hi.symm.trans hj)
    apply hne
    cases p
    cases q
    congr
    · exact hpg.trans hqg.symm
  · change bundleValue w (packetGoods P.toFinset) = bundleValue w R
    apply Finset.sum_subset hsub
    intro g hg hout
    rw [hw g]
    cases he : tag g with
    | none => rfl
    | some lvl =>
      have hm : (⟨{g}, lvl⟩ : Packet m) ∈ P := mem_initialPackets.mpr ⟨g, hg, he, rfl⟩
      exact (hout (Finset.mem_biUnion.mpr ⟨_, List.mem_toFinset.mpr hm,
        Finset.mem_singleton_self g⟩)).elim

/-- Perform the packet merges and keep exactly the menu specified in the
proof, in deterministic list order. -/
def preparedMenu {m : ℕ} (tag : Fin m → Option PacketLevel) (R : Finset (Fin m))
    (r : ℕ) : List (Finset (Fin m)) :=
  let P := initialPackets tag R
  packetMenu R r (normalizePackets P.length P).1

theorem preparedMenu_spec {m r : ℕ} (tag : Fin m → Option PacketLevel) (R : Finset (Fin m))
    (w : Fin m → ℝ) (hw : ∀ g, w g = (tag g).elim 0 PacketLevel.weight)
    (hR : (r : ℝ) ≤ bundleValue w R) :
    let B := preparedMenu tag R r
    B.length = r ∧ B.Pairwise Disjoint ∧ ∀ G ∈ B,
      G ⊆ R ∧ 1 ≤ bundleValue w G ∧ (r : ℝ) - 1 ≤ bundleValue w (R \ G) := by
  obtain ⟨hP, hv, hsub, hmass⟩ := initialPackets_spec tag R w hw
  let P := initialPackets tag R
  have h := normalizePackets_spec P.length P hP hv le_rfl
  rcases he : normalizePackets P.length P with ⟨Q, count⟩
  rw [he] at h
  let good (B : List (Finset (Fin m))) := B.length = r ∧ B.Pairwise Disjoint ∧ ∀ G ∈ B,
    G ⊆ R ∧ 1 ≤ bundleValue w G ∧ (r : ℝ) - 1 ≤ bundleValue w (R \ G)
  change good (packetMenu R r (normalizePackets P.length P).1)
  rw [he]
  exact packetMenu_spec h.1 h.2.1 h.2.2.2.1 (h.2.2.1 ▸ hsub)
    (h.2.2.1 ▸ hmass) hR

def otherType (t : Fin 2) : Fin 2 := if t = 0 then 1 else 0

private theorem same_or_other_type (t i : Fin 2) : i = t ∨ i = otherType t := by
  fin_cases t <;> fin_cases i <;> simp [otherType]

/-- The actual current move. The other type's score is compared in exact
rational arithmetic. -/
def packetChoice {m : ℕ} (scale : Fin 2 → ℚ) (tag : Fin 2 → Fin m → Option PacketLevel)
    (r : ℕ) (R : Finset (Fin m)) (t : Fin 2) : Finset (Fin m) :=
  if r ≤ 1 then R
  else if scale t ≤ 0 then ∅
  else
    let B := preparedMenu (tag t) R r
    (B.argmin (fun G => ∑ g ∈ G, (tag (otherType t) g).elim 0 PacketLevel.weightRat)).getD ∅

/-- Policy tree for the packet rule. A move uses only the revealed type and
the remaining goods, so execution needs no look-ahead or counts. -/
def packetPolicy {m : ℕ} (scale : Fin 2 → ℚ) (tag : Fin 2 → Fin m → Option PacketLevel) :
    (r : ℕ) → Finset (Fin m) → Policy m 2 r
  | 0, _ => .done
  | r + 1, R => .step (packetChoice scale tag (r + 1) R)
      (fun t => packetPolicy scale tag r (R \ packetChoice scale tag (r + 1) R t))

private theorem cheapest_list_cost {m : ℕ} {menu : List (Finset (Fin m))}
    (hp : menu.Pairwise Disjoint) {w : Fin m → ℝ} (hw : ∀ g, 0 ≤ w g)
    {G R : Finset (Fin m)} (hmin : ∀ B ∈ menu, bundleValue w G ≤ bundleValue w B)
    (hsub : ∀ B ∈ menu, B ⊆ R) :
    (menu.length : ℝ) * bundleValue w G ≤ bundleValue w R := by
  classical
  let B (i : Fin menu.length) := menu.get i
  calc
    _ = ∑ _i : Fin menu.length, bundleValue w G := by simp [nsmul_eq_mul]
    _ ≤ ∑ i : Fin menu.length, bundleValue w (B i) :=
      Finset.sum_le_sum fun i _ => hmin (B i) (menu.get_mem i)
    _ = bundleValue w (Finset.univ.biUnion B) := by
      unfold bundleValue
      rw [Finset.sum_biUnion]
      intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact List.pairwise_iff_get.mp hp i j h
      · exact (List.pairwise_iff_get.mp hp j i h).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun g _ _ => hw g)
      intro g hg
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
      exact hsub (B i) (menu.get_mem i) hi

/-- Any admissible scales can be used with the literal executable merge
and minimum-cost selection routine. -/
theorem packetPolicy_guarantees {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (scale : Fin 2 → ℚ) (hs : ∀ t, 0 ≤ scale t)
    (tag : Fin 2 → Fin m → Option PacketLevel)
    (htag : ∀ t g, score (v t g / (scale t : ℝ)) = (tag t g).elim 0 PacketLevel.weight)
    (r : ℕ) (R : Finset (Fin m))
    (hR : ∀ t, 0 < scale t → (r : ℝ) ≤ bundleValue
      (fun g => score (v t g / (scale t : ℝ))) R) :
    (packetPolicy scale tag r R).Guarantees v (fun t => (scale t : ℝ)) R := by
  classical
  let w (t : Fin 2) (g : Fin m) := score (v t g / (scale t : ℝ))
  have hx (t : Fin 2) (g : Fin m) : 0 ≤ v t g / (scale t : ℝ) :=
    div_nonneg (hv t g) (by exact_mod_cast hs t)
  have hw (t : Fin 2) (g : Fin m) : 0 ≤ w t g := score_nonneg (hx t g)
  have hpay (t : Fin 2) (ht : 0 < scale t) (G : Finset (Fin m))
      (hG : 1 ≤ bundleValue (w t) G) : (scale t : ℝ) ≤ bundleValue (v t) G := by
    have htR : (0 : ℝ) < (scale t : ℝ) := by exact_mod_cast ht
    calc
      (scale t : ℝ) ≤ (scale t : ℝ) * bundleValue (w t) G := by
        simpa using mul_le_mul_of_nonneg_left hG htR.le
      _ = ∑ g ∈ G, (scale t : ℝ) * w t g := Finset.mul_sum ..
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro g _
        simpa [mul_div_cancel₀ _ htR.ne'] using
          mul_le_mul_of_nonneg_left (score_le_value (hx t g)) htR.le
  induction r generalizing R with
  | zero => trivial
  | succ r ih =>
    intro t
    change packetChoice scale tag (r + 1) R t ⊆ R ∧
      (scale t : ℝ) ≤ bundleValue (v t) (packetChoice scale tag (r + 1) R t) ∧
      (packetPolicy scale tag r (R \ packetChoice scale tag (r + 1) R t)).Guarantees
        v (fun t => (scale t : ℝ)) (R \ packetChoice scale tag (r + 1) R t)
    by_cases hr : r = 0
    · subst r
      rw [show packetChoice scale tag 1 R t = R by simp [packetChoice]]
      refine ⟨Finset.Subset.rfl, ?_, trivial⟩
      by_cases ht : 0 < scale t
      · exact hpay t ht R (by simpa using hR t ht)
      · have hzero : scale t = 0 := le_antisymm (le_of_not_gt ht) (hs t)
        simp [hzero, bundleValue, Finset.sum_nonneg (fun g _ => hv t g)]
    · have hr' : ¬ r + 1 ≤ 1 := by omega
      by_cases ht : 0 < scale t
      · let menu := preparedMenu (tag t) R (r + 1)
        have hmenu := preparedMenu_spec (tag t) R (w t) (htag t) (hR t ht)
        change menu.length = r + 1 ∧ menu.Pairwise Disjoint ∧ ∀ G ∈ menu, _ at hmenu
        let cost (G : Finset (Fin m)) :=
          ∑ g ∈ G, (tag (otherType t) g).elim 0 PacketLevel.weightRat
        have hcost (G : Finset (Fin m)) : (cost G : ℝ) = bundleValue (w (otherType t)) G := by
          unfold cost bundleValue
          push_cast
          apply Finset.sum_congr rfl
          intro g _
          dsimp [w]
          rw [htag]
          cases tag (otherType t) g <;> simp
        cases he : menu.argmin cost with
        | none =>
          have hempty := List.argmin_eq_none.mp he
          simp [hempty] at hmenu
        | some G =>
          have hmin := List.argmin_eq_some_iff.mp he
          have hchoice : packetChoice scale tag (r + 1) R t = G := by
            unfold packetChoice
            rw [if_neg hr', if_neg (not_le_of_gt ht)]
            change (menu.argmin cost).getD ∅ = G
            simp [he]
          rw [hchoice]
          obtain ⟨hsub, hown, hleave⟩ := hmenu.2.2 G hmin.1
          refine ⟨hsub, hpay t ht G hown, ih _ ?_⟩
          intro i hi
          rcases same_or_other_type t i with rfl | rfl
          · simpa only [Nat.cast_succ, add_sub_cancel_right] using hleave
          · have hc := cheapest_list_cost hmenu.2.1 (hw (otherType t))
                (fun B hB => by rw [← hcost G, ← hcost B]; exact_mod_cast hmin.2.1 B hB)
                (fun B hB => (hmenu.2.2 B hB).1)
            rw [hmenu.1, Nat.cast_succ] at hc
            have hsum : bundleValue (w (otherType t)) (R \ G) + bundleValue (w (otherType t)) G =
                bundleValue (w (otherType t)) R := Finset.sum_sdiff hsub
            have hprev := hR (otherType t) hi
            change ((r + 1 : ℕ) : ℝ) ≤ bundleValue (w (otherType t)) R at hprev
            rw [Nat.cast_succ] at hprev
            have hmul := mul_le_mul_of_nonneg_left hprev (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
            have hp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
            change (r : ℝ) ≤ bundleValue (w (otherType t)) (R \ G)
            apply (mul_le_mul_left hp).mp
            have heq : ((r : ℝ) + 1) * (bundleValue (w (otherType t)) (R \ G) +
                bundleValue (w (otherType t)) G) =
                ((r : ℝ) + 1) * bundleValue (w (otherType t)) R :=
              congrArg _ hsum
            nlinarith only [hc, hmul, heq]
      · have hzero : scale t = 0 := le_antisymm (le_of_not_gt ht) (hs t)
        rw [show packetChoice scale tag (r + 1) R t = ∅ by simp [packetChoice, hr', hzero]]
        refine ⟨Finset.empty_subset _, by simp [hzero, bundleValue], ih _ ?_⟩
        intro i hi
        rw [Finset.sdiff_empty]
        exact (by exact_mod_cast Nat.le_succ r : (r : ℝ) ≤ ↑(r + 1)).trans (hR i hi)

end OnlineMMS.TwoType
