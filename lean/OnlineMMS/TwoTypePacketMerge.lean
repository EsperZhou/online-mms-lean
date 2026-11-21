import OnlineMMS.TwoTypePacking
import Mathlib.Data.Finset.Card

namespace OnlineMMS.TwoType

/-- Positive score levels, with units explicitly kept out of all merges. -/
inductive PacketLevel
  | unit
  | half (j : ℕ)
  | third (j : ℕ)
  deriving DecidableEq

noncomputable def PacketLevel.weight : PacketLevel → ℝ
  | .unit => 1
  | .half j => dyadic (j + 1)
  | .third j => thirds j

def PacketLevel.carry : PacketLevel → Option (ℕ × PacketLevel)
  | .unit => none
  | .half 0 => some (2, .unit)
  | .half (j + 1) => some (2, .half j)
  | .third 0 => some (3, .unit)
  | .third (j + 1) => some (2, .third j)

theorem PacketLevel.carry_spec {a b : PacketLevel} {d : ℕ}
    (h : a.carry = some (d, b)) : 2 ≤ d ∧ (d : ℝ) * a.weight = b.weight := by
  have hs (j : ℕ) : dyadic (j + 1) = dyadic j / 2 := by
    simp only [dyadic, pow_succ, div_div]
  cases a with
  | unit => simp [carry] at h
  | half j =>
    cases j with
    | zero =>
      simp [carry] at h
      obtain ⟨rfl, rfl⟩ := h
      norm_num [weight, dyadic]
    | succ j =>
      simp [carry] at h
      obtain ⟨rfl, rfl⟩ := h
      constructor
      · decide
      · simp only [weight, Nat.cast_ofNat]
        rw [hs (j + 1)]
        ring
  | third j =>
    cases j with
    | zero =>
      simp [carry] at h
      obtain ⟨rfl, rfl⟩ := h
      norm_num [weight, thirds, dyadic]
    | succ j =>
      simp [carry] at h
      obtain ⟨rfl, rfl⟩ := h
      constructor
      · decide
      · simp only [weight, Nat.cast_ofNat, thirds]
        rw [hs]
        ring

structure Packet (m : ℕ) where
  goods : Finset (Fin m)
  level : PacketLevel
  deriving DecidableEq

def packetGoods {m : ℕ} (P : Finset (Packet m)) : Finset (Fin m) :=
  P.biUnion Packet.goods

structure ValidPackets {m : ℕ} (w : Fin m → ℝ) (P : Finset (Packet m)) : Prop where
  nonempty : ∀ p ∈ P, p.goods.Nonempty
  weight : ∀ p ∈ P, bundleValue w p.goods = p.level.weight
  separate : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p.goods q.goods

/-- One literal pair or triple merge from the manuscript. All permissible
tie resolutions use this same step relation. -/
structure PacketMerge {m : ℕ} (P Q : Finset (Packet m)) : Prop where
  witness : ∃ (take : Finset (Packet m)) (src dest : PacketLevel) (arity : ℕ),
    take ⊆ P ∧ src.carry = some (arity, dest) ∧ take.card = arity ∧
      (∀ p ∈ take, p.level = src) ∧
      Q = insert ⟨packetGoods take, dest⟩ (P \ take)

private theorem packetGoods_subset {m : ℕ} {P Q : Finset (Packet m)} (h : P ⊆ Q) :
    packetGoods P ⊆ packetGoods Q := by
  intro g hg
  obtain ⟨p, hp, hpg⟩ := Finset.mem_biUnion.mp hg
  exact Finset.mem_biUnion.mpr ⟨p, h hp, hpg⟩

theorem PacketMerge.valid {m : ℕ} {w : Fin m → ℝ} {P Q : Finset (Packet m)}
    (hs : PacketMerge P Q) (hv : ValidPackets w P) :
    ValidPackets w Q ∧ packetGoods Q = packetGoods P ∧ Q.card < P.card := by
  classical
  obtain ⟨take, src, dest, arity, hsub, hcarry, hcard, hfrom, rfl⟩ := hs.witness
  let p : Packet m := ⟨packetGoods take, dest⟩
  let rest := P \ take
  have harity := PacketLevel.carry_spec hcarry
  have hn : take.Nonempty := Finset.card_pos.mp (by omega)
  have hp : p.goods.Nonempty := by
    obtain ⟨x, hx⟩ := hn
    exact (hv.nonempty x (hsub hx)).mono (fun g hg => Finset.mem_biUnion.mpr ⟨x, hx, hg⟩)
  have hrest (q : Packet m) (hq : q ∈ rest) : Disjoint p.goods q.goods := by
    apply Finset.disjoint_left.mpr
    intro g hg hqg
    obtain ⟨x, hx, hxg⟩ := Finset.mem_biUnion.mp hg
    have he : x ≠ q := fun e => (Finset.mem_sdiff.mp hq).2 (e ▸ hx)
    exact Finset.disjoint_left.mp (hv.separate x (hsub hx) q (Finset.mem_sdiff.mp hq).1 he) hxg hqg
  have hweight : bundleValue w p.goods = p.level.weight := by
    unfold bundleValue
    change ∑ g ∈ take.biUnion Packet.goods, w g = dest.weight
    rw [Finset.sum_biUnion]
    · calc
        ∑ q ∈ take, (∑ g ∈ q.goods, w g) = ∑ _q ∈ take, src.weight := by
          apply Finset.sum_congr rfl
          intro q hq
          change bundleValue w q.goods = src.weight
          rw [hv.weight q (hsub hq), hfrom q hq]
        _ = dest.weight := by simpa [hcard, nsmul_eq_mul] using harity.2
    · exact fun x hx y hy hne => hv.separate x (hsub hx) y (hsub hy) hne
  change ValidPackets w (insert p rest) ∧ packetGoods (insert p rest) = packetGoods P ∧
    (insert p rest).card < P.card
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hv.nonempty q (Finset.mem_sdiff.mp hq).1
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hweight
    · exact hv.weight q (Finset.mem_sdiff.mp hq).1
  · intro x hx y hy hne
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hne rfl).elim
      · exact hrest y hy
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hrest x hx).symm
      · exact hv.separate x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hne
  · ext g
    constructor
    · intro hg
      obtain ⟨q, hq, hqg⟩ := Finset.mem_biUnion.mp hg
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact packetGoods_subset hsub hqg
      · exact Finset.mem_biUnion.mpr ⟨q, (Finset.mem_sdiff.mp hq).1, hqg⟩
    · intro hg
      obtain ⟨q, hq, hqg⟩ := Finset.mem_biUnion.mp hg
      by_cases ht : q ∈ take
      · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_insert_self p rest,
          Finset.mem_biUnion.mpr ⟨q, ht, hqg⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hq, ht⟩), hqg⟩
  · have he := Finset.card_sdiff_add_card_eq_card hsub
    change rest.card + take.card = P.card at he
    have hle := Finset.card_insert_le p rest
    omega

def PacketsTerminal {m : ℕ} (P : Finset (Packet m)) : Prop := ∀ Q, ¬ PacketMerge P Q

/-- If no merge is available, each nonunit level holds fewer than its
carry threshold. -/
theorem PacketsTerminal.below_carry {m : ℕ} {P : Finset (Packet m)}
    (hP : PacketsTerminal P) {src dest : PacketLevel} {arity : ℕ}
    (hcarry : src.carry = some (arity, dest)) :
    (P.filter (fun p => p.level = src)).card < arity := by
  classical
  by_contra! h
  obtain ⟨take, htake, hcard⟩ := Finset.exists_subset_card_eq h
  have hsub := htake.trans (Finset.filter_subset _ _)
  exact hP _ ⟨⟨take, src, dest, arity, hsub, hcarry, hcard,
    fun p hp => (Finset.mem_filter.mp (htake hp)).2, rfl⟩⟩

theorem validPackets_mass {m : ℕ} {P : Finset (Packet m)} {w : Fin m → ℝ}
    (hv : ValidPackets w P) :
    bundleValue w (packetGoods P) = ∑ p ∈ P, p.level.weight := by
  classical
  unfold bundleValue packetGoods
  rw [Finset.sum_biUnion hv.separate]
  exact Finset.sum_congr rfl hv.weight

end OnlineMMS.TwoType
