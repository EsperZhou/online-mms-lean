import OnlineMMS.BinaryPatterns
import OnlineMMS.BinarySupport

namespace OnlineMMS

variable {G : Type*} [DecidableEq G]

private theorem card_filter_insert_eq (S : Finset G) (a : G) (ha : a ∉ S)
    (P : G → Prop) [DecidablePred P] :
    ((insert a S).filter P).card = (S.filter P).card + if P a then 1 else 0 := by
  classical
  by_cases hp : P a
  · have hnot : a ∉ S.filter P := Finset.not_mem_mono (Finset.filter_subset _ _) ha
    rw [Finset.filter_insert, if_pos hp, if_pos hp, Finset.card_insert_of_not_mem hnot]
  · simp [Finset.filter_insert, hp]

omit [DecidableEq G] in
private theorem image_filter_pattern (f : G → ApprovalPattern) (S : Finset G) (i : Fin 5) :
    (S.filter (fun g => i ∈ f g)).image f = (S.image f).filter (i ∈ ·) := by
  ext P
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    exact ⟨⟨g, hg, rfl⟩, hi⟩
  · rintro ⟨⟨g, hg, rfl⟩, hi⟩
    exact ⟨g, ⟨hg, hi⟩, rfl⟩

/-- A first bundle of the required size and its five approval constraints. -/
def IsBalancedHalf (f : G → ApprovalPattern) (S X : Finset G) : Prop :=
  X ⊆ S ∧ X.card = S.card / 2 ∧
    ∀ i : Fin 5, (X.filter (fun g => i ∈ f g)).card ≤
      ((S.filter (fun g => i ∈ f g)).card + 1) / 2

/-- Removing a comparable pair and allocating the smaller pattern preserves balance. -/
theorem balanced_half_step (f : G → ApprovalPattern) (S : Finset G)
    (a b : G) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) (hsub : f a ⊆ f b)
    (Y : Finset G) (hy : IsBalancedHalf f (S \ {a, b}) Y) :
    IsBalancedHalf f S (insert a Y) := by
  classical
  let T := S \ {a, b}
  obtain ⟨hY, hYc, hy⟩ := hy
  change Y ⊆ T at hY
  change Y.card = T.card / 2 at hYc
  have hT : T ⊆ S := Finset.sdiff_subset
  have hna : a ∉ T := by simp [T]
  have hnb : b ∉ T := by simp [T]
  have hS : insert a (insert b T) = S := by
    ext g
    by_cases hga : g = a
    · subst g; simp [ha]
    by_cases hgb : g = b
    · subst g; simp [hb]
    simp [T, hga, hgb]
  have hcard : S.card = T.card + 2 := by
    have hnot : a ∉ insert b T := by simp [hne, hna]
    rw [← hS, Finset.card_insert_of_not_mem hnot, Finset.card_insert_of_not_mem hnb]
  have hnya : a ∉ Y := fun h => hna (hY h)
  refine ⟨Finset.insert_subset ha (hY.trans hT), ?_, ?_⟩
  · rw [Finset.card_insert_of_not_mem hnya, hYc, hcard]
    omega
  · intro i
    let P : G → Prop := fun g => i ∈ f g
    have hnot : a ∉ insert b T := by simp [hne, hna]
    have hS' : (S.filter P).card =
        (T.filter P).card + (if P b then 1 else 0) + (if P a then 1 else 0) := by
      rw [← hS, card_filter_insert_eq _ _ hnot P, card_filter_insert_eq _ _ hnb P]
    change ((insert a Y).filter P).card ≤ ((S.filter P).card + 1) / 2
    rw [card_filter_insert_eq _ _ hnya P, hS']
    have hh : (Y.filter P).card ≤ ((T.filter P).card + 1) / 2 := hy i
    by_cases hpa : P a
    · have hpb : P b := hsub hpa
      simp only [if_pos hpa, if_pos hpb]
      omega
    · rw [if_neg hpa]
      split <;> omega

omit [DecidableEq G] in
/-- Distinct goods with no comparable pair map injectively into the five-bit patterns. -/
theorem pattern_injective_of_no_pair (f : G → ApprovalPattern) (S : Finset G)
    (hpair : ¬ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a ⊆ f b) :
    Set.InjOn f (S : Set G) := by
  intro a ha b hb h
  by_contra hne
  exact hpair ⟨a, ha, b, hb, hne, h.le⟩

omit [DecidableEq G] in
/-- The terminal case is balanced by the five-coordinate catalogue. -/
theorem balanced_half_no_pair (f : G → ApprovalPattern) (S : Finset G)
    (hpair : ¬ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a ⊆ f b) :
    ∃ X, IsBalancedHalf f S X := by
  classical
  have hinj := pattern_injective_of_no_pair f S hpair
  have hanti : IsApprovalAntichain (S.image f) := by
    intro A hA B hB hneq hsub
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    exact hpair ⟨a, ha, b, hb, fun h => hneq (congrArg f h), hsub⟩
  obtain ⟨C, hC, hCc, hbal⟩ := five_approval_coordinates (S.image f) hanti
  let X := S.filter (fun g => f g ∈ C)
  have hX : X ⊆ S := Finset.filter_subset _ _
  have him : X.image f = C := by
    ext P
    constructor
    · rintro h
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hg).2
    · intro h
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (hC h)
      exact Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, h⟩, rfl⟩
  have hcard (Y : Finset G) (hY : Y ⊆ S) : (Y.image f).card = Y.card :=
    Finset.card_image_of_injOn (hinj.mono (by simpa using hY))
  refine ⟨X, hX, ?_, ?_⟩
  · rw [← hcard X hX, him, hCc, hcard S Finset.Subset.rfl]
  · intro i
    have hl := hcard (X.filter (fun g => i ∈ f g))
      ((Finset.filter_subset _ _).trans hX)
    have hr := hcard (S.filter (fun g => i ∈ f g)) (Finset.filter_subset _ _)
    rw [image_filter_pattern, him] at hl
    rw [image_filter_pattern] at hr
    simpa only [hl, hr] using hbal i

/-- Pairing comparable patterns reduces every set of goods to an antichain. -/
private theorem balanced_half_goods (f : G → ApprovalPattern) (S : Finset G) :
    ∃ X, IsBalancedHalf f S X := by
  classical
  by_cases hpair : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a ⊆ f b
  · obtain ⟨a, ha, b, hb, hne, hsub⟩ := hpair
    let T := S \ {a,b}
    have hT : T ⊆ S := Finset.sdiff_subset
    have hna : a ∉ T := by simp [T]
    have hlt : T.card < S.card := Finset.card_lt_card
      ((Finset.ssubset_iff_of_subset hT).mpr ⟨a, ha, hna⟩)
    obtain ⟨Y, hy⟩ := balanced_half_goods f T
    exact ⟨_, balanced_half_step f S a b ha hb hne hsub Y hy⟩
  · exact balanced_half_no_pair f S hpair
termination_by S.card

private theorem binaryDemand_one (a : ℕ) : binaryDemand a 1 = a / 2 := by
  apply le_antisymm (binaryDemand_le_half a (by decide))
  simpa using binaryDemand_pays a (p := 1) (by decide)

/-- A balanced half of the approved goods pays the full MMS of both arrivals. -/
theorem binary_small_bundle_of_balanced {m k : ℕ}
    (S : Fin k → Finset (Fin m)) (first : Fin k)
    (pattern : Fin m → ApprovalPattern)
    (hpattern : ∀ t : Fin k, t ≠ first → ∃ i : Fin 5, ∀ g, i ∈ pattern g ↔ g ∈ S t)
    (X : Finset (Fin m)) (hX : IsBalancedHalf pattern (S first) X) :
    X ⊆ S first ∧ binaryDemand (S first).card 1 ≤ X.card ∧
      ∀ t, binaryDemand (S t).card 1 ≤ (S t \ X).card := by
  classical
  obtain ⟨hX, hXc, hbal⟩ := hX
  refine ⟨hX, (binaryDemand_one _).le.trans hXc.ge, ?_⟩
  intro t
  rw [binaryDemand_one]
  by_cases ht : t = first
  · subst t
    have hh := Finset.card_sdiff_add_card_eq_card hX
    omega
  · obtain ⟨i, hi⟩ := hpattern t ht
    have hy := hbal i
    simp only [hi] at hy
    change (X.filter (fun g => g ∈ S t)).card ≤
      (((S first).filter (fun g => g ∈ S t)).card + 1) / 2 at hy
    have hle : ((S first).filter (fun g => g ∈ S t)).card ≤ (S t).card :=
      Finset.card_le_card (fun g hg => (Finset.mem_filter.mp hg).2)
    have hpart : (X.filter (fun g => g ∈ S t)).card + (S t \ X).card = (S t).card := by
      have heq : X.filter (fun g => g ∈ S t) = S t ∩ X := by
        ext g; simp [and_comm]
      rw [heq]
      exact Finset.card_inter_add_card_sdiff _ _
    omega

/-- The five-coordinate argument attains full MMS for every first arrival
and all possible second arrivals when at most six types are listed. -/
theorem binary_small_bundle {m k : ℕ} (hk : k ≤ 6)
    (S : Fin k → Finset (Fin m)) (first : Fin k) :
    ∃ X ⊆ S first, binaryDemand (S first).card 1 ≤ X.card ∧
      ∀ t, binaryDemand (S t).card 1 ≤ (S t \ X).card := by
  classical
  let other := (Finset.univ : Finset (Fin k)).erase first
  have hbound : other.card ≤ 5 := by
    dsimp [other]
    rw [Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
    omega
  let index : (↑other : Type) → Fin 5 := fun t =>
    Fin.castLE hbound (other.equivFin t)
  have hindex : Function.Injective index :=
    (Fin.castLE_injective hbound).comp other.equivFin.injective
  let pattern (g : Fin m) : ApprovalPattern :=
    (other.attach.filter (fun t => g ∈ S t.val)).image index
  have hpattern (t : ↑other) (g : Fin m) : index t ∈ pattern g ↔ g ∈ S t.val := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
      have he' := hindex he
      subst u
      exact (Finset.mem_filter.mp hu).2
    · intro h
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, h⟩, rfl⟩
  obtain ⟨X, hX⟩ := balanced_half_goods pattern (S first)
  refine ⟨X, binary_small_bundle_of_balanced S first pattern ?_ X hX⟩
  intro t ht
  let u : ↑other := ⟨t, Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩⟩
  exact ⟨index u, hpattern u⟩

theorem binary_small_guarantee {m k : ℕ} (hk : k ≤ 6)
    (S : Fin k → Finset (Fin m)) :
    ∃ policy : Policy m k 2, policy.Guarantees (fun t => approvalValue (S t))
      (fun t => maximinShare (approvalValue (S t)) 2 (by decide)) Finset.univ := by
  obtain ⟨policy, hp⟩ := binary_policy_of_demands (p := 1) (by decide) S (binary_small_bundle hk S)
  exact ⟨policy, by simpa using hp⟩

end OnlineMMS
