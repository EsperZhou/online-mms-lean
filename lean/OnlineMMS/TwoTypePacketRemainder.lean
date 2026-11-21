import OnlineMMS.TwoTypePacketMerge

namespace OnlineMMS.TwoType

private theorem dyadic_prefix_sum (L : ℕ) :
    (∑ j ∈ Finset.range L, dyadic (j + 1)) = 1 - dyadic L := by
  induction L with
  | zero => simp [dyadic]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have h : dyadic (L + 1) = dyadic L / 2 := by
      simp only [dyadic, pow_succ, div_div]
    linarith

private theorem family_mass_le {m : ℕ} {P S : Finset (Packet m)}
    (hsub : S ⊆ P) (tag : ℕ → PacketLevel) (idx : Packet m → ℕ)
    (htag : ∀ p ∈ S, p.level = tag (idx p))
    (hcap : ∀ j, (P.filter fun p => p.level = tag j).card ≤ 1)
    (hnonneg : ∀ j, 0 ≤ (tag j).weight) :
    ∑ p ∈ S, p.level.weight ≤ ∑ j ∈ Finset.range (S.sup idx + 1), (tag j).weight := by
  classical
  have hm (p : Packet m) (hp : p ∈ S) : idx p ∈ Finset.range (S.sup idx + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := idx) hp))
  calc
    ∑ p ∈ S, p.level.weight = ∑ p ∈ S, (tag (idx p)).weight :=
      Finset.sum_congr rfl (fun p hp => by rw [htag p hp])
    _ = ∑ j ∈ Finset.range (S.sup idx + 1),
          ∑ p ∈ S with idx p = j, (tag j).weight :=
      (Finset.sum_fiberwise_of_maps_to' hm (fun j => (tag j).weight)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      have hc : (S.filter fun p => idx p = j).card ≤ 1 := by
        have hs : (S.filter (fun p => idx p = j)) ⊆ P.filter (fun p => p.level = tag j) := by
          intro p hp
          obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨hsub hp, (htag p hp).trans (congrArg tag he)⟩
        exact (Finset.card_le_card hs).trans (hcap j)
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcR : (((S.filter fun p => idx p = j).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
      nlinarith only [mul_le_mul_of_nonneg_right hcR (hnonneg j)]

/-- The two unmerged families each have strictly less than one unit of
score. In the third family the two possible level-zero packets contribute
at most 2/3. -/
theorem terminal_nonunit_mass_lt_two {m : ℕ} {P : Finset (Packet m)}
    (hP : PacketsTerminal P) :
    ∑ p ∈ P with p.level ≠ .unit, p.level.weight < 2 := by
  classical
  let H := P.filter (fun p => ∃ j, p.level = .half j)
  let T := P.filter (fun p => ∃ j, p.level = .third (j + 1))
  let Z := P.filter (fun p => p.level = .third 0)
  let iH (p : Packet m) := match p.level with
    | .half j => j
    | _ => 0
  let iT (p : Packet m) := match p.level with
    | .third j => j - 1
    | _ => 0
  have hH : ∑ p ∈ H, p.level.weight < 1 := by
    have hsub : H ⊆ P := Finset.filter_subset _ _
    have hle := family_mass_le hsub PacketLevel.half iH
      (fun p hp => by
        have hmem : p ∈ P.filter (fun p => ∃ j, p.level = .half j) := hp
        obtain ⟨j, he⟩ := (Finset.mem_filter.mp hmem).2
        simp [iH, he])
      (fun j => by
        cases j with
        | zero => exact Nat.le_of_lt_succ (hP.below_carry (by rfl : (PacketLevel.half 0).carry = some (2, .unit)))
        | succ j => exact Nat.le_of_lt_succ (hP.below_carry (by rfl : (PacketLevel.half (j + 1)).carry = some (2, .half j))))
      (fun j => by unfold PacketLevel.weight dyadic; positivity)
    simp only [PacketLevel.weight, dyadic_prefix_sum] at hle
    exact hle.trans_lt (sub_lt_self _ (by unfold dyadic; positivity))
  have hT : ∑ p ∈ T, p.level.weight < 1 / 3 := by
    have hsub : T ⊆ P := Finset.filter_subset _ _
    have hle := family_mass_le hsub (fun j => PacketLevel.third (j + 1)) iT
      (fun p hp => by
        have hmem : p ∈ P.filter (fun p => ∃ j, p.level = .third (j + 1)) := hp
        obtain ⟨j, he⟩ := (Finset.mem_filter.mp hmem).2
        simp [iT, he])
      (fun j => Nat.le_of_lt_succ (hP.below_carry
        (by rfl : (PacketLevel.third (j + 1)).carry = some (2, .third j))))
      (fun j => by unfold PacketLevel.weight thirds dyadic; positivity)
    simp only [PacketLevel.weight, thirds, ← Finset.sum_div, dyadic_prefix_sum] at hle
    change (∑ p ∈ T, p.level.weight) ≤ (1 - dyadic (T.sup iT + 1)) / 3 at hle
    have hp : 0 < dyadic (T.sup iT + 1) := by unfold dyadic; positivity
    linarith
  have hZ : ∑ p ∈ Z, p.level.weight ≤ 2 / 3 := by
    have hc : Z.card ≤ 2 := Nat.le_of_lt_succ (hP.below_carry
      (by rfl : (PacketLevel.third 0).carry = some (3, .unit)))
    have hcR : (Z.card : ℝ) ≤ 2 := by exact_mod_cast hc
    calc
      ∑ p ∈ Z, p.level.weight = ∑ _p ∈ Z, (1 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
        norm_num [PacketLevel.weight, thirds, dyadic]
      _ ≤ _ := by simp only [Finset.sum_const, nsmul_eq_mul]; linarith
  have hsplit : (∑ p ∈ P with p.level ≠ .unit, p.level.weight) =
      (∑ p ∈ H, p.level.weight) + (∑ p ∈ T, p.level.weight) + (∑ p ∈ Z, p.level.weight) := by
    dsimp [H, T, Z]
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    cases he : p.level with
    | unit => simp
    | half j => simp
    | third j => cases j <;> simp
  linarith

end OnlineMMS.TwoType
