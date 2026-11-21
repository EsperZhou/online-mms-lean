import OnlineMMS.TwoTypeScore
import Mathlib.Data.Finset.Powerset

namespace OnlineMMS.TwoType

private theorem unit_multiple {m : ℕ} (w : Fin m → ℝ) (R : Finset (Fin m))
    (hpos : ∀ g ∈ R, 0 < w g)
    (hunit : ∀ g ∈ R, ∃ j : ℕ, (j : ℝ) * w g = 1)
    (hdiv : ∀ g ∈ R, ∀ h ∈ R, w g ≤ w h → ∃ j : ℕ, (j : ℝ) * w g = w h)
    (htotal : 1 ≤ bundleValue w R) :
    ∃ B ⊆ R, bundleValue w B = 1 := by
  classical
  let pool := R.powerset.filter (fun B => 1 ≤ bundleValue w B)
  have hnp : pool.Nonempty := ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, htotal⟩⟩
  obtain ⟨B, hB, hmin⟩ := pool.exists_min_image Finset.card hnp
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hmass := (Finset.mem_filter.mp hB).2
  have hnB : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hmass
    norm_num [bundleValue] at hmass
  obtain ⟨g, hg, hsmall⟩ := B.exists_min_image w hnB
  have hgap : bundleValue w (B.erase g) < 1 := by
    apply lt_of_not_ge
    intro hl
    have hmem : B.erase g ∈ pool := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub), hl⟩
    exact (Nat.not_lt_of_ge (hmin _ hmem)) (Finset.card_erase_lt_of_mem hg)
  have hsum := Finset.sum_erase_add B w hg
  change bundleValue w (B.erase g) + w g = bundleValue w B at hsum
  have hBlt : bundleValue w B < 1 + w g := by linarith
  obtain ⟨j, hj⟩ := hunit g (hsub hg)
  have hcoins (i : Fin m) : ∃ q : ℕ, i ∈ B → (q : ℝ) * w g = w i := by
    by_cases hi : i ∈ B
    · obtain ⟨q, hq⟩ := hdiv g (hsub hg) i (hsub hi) (hsmall i hi)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose coins hcoins using hcoins
  have hform : ((∑ i ∈ B, coins i : ℕ) : ℝ) * w g = bundleValue w B := by
    unfold bundleValue
    rw [Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => hcoins i hi)
  have hposg := hpos g (hsub hg)
  have hge : (j : ℝ) ≤ ((∑ i ∈ B, coins i : ℕ) : ℝ) := by
    apply (mul_le_mul_right hposg).mp
    rwa [hj, hform]
  have hlt : ((∑ i ∈ B, coins i : ℕ) : ℝ) < (j : ℝ) + 1 := by
    apply (mul_lt_mul_right hposg).mp
    rw [hform, add_mul, hj, one_mul]
    exact hBlt
  have hgeN : j ≤ ∑ i ∈ B, coins i := by exact_mod_cast hge
  have hltN : (∑ i ∈ B, coins i) < j + 1 := by exact_mod_cast hlt
  have he : (∑ i ∈ B, coins i) = j := by omega
  rw [he, hj] at hform
  exact ⟨B, hsub, hform.symm⟩

private theorem weighted_family_unit {m : ℕ} (R : Finset (Fin m)) (w : Fin m → ℝ)
    (c : ℕ) (hc : 0 < c)
    (hlevel : ∀ g ∈ R, ∃ j : ℕ, w g = 1 / ((c : ℝ) * 2 ^ j))
    (htotal : 1 ≤ bundleValue w R) :
    ∃ G ⊆ R, bundleValue w G = 1 := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  apply unit_multiple w R
  · intro g hg
    obtain ⟨j, hj⟩ := hlevel g hg
    rw [hj]
    positivity
  · intro g hg
    obtain ⟨j, hj⟩ := hlevel g hg
    refine ⟨c * 2 ^ j, ?_⟩
    rw [hj]
    push_cast
    field_simp
  · intro g hg h hh hgh
    obtain ⟨i, hi⟩ := hlevel g hg
    obtain ⟨j, hj⟩ := hlevel h hh
    have hjle : j ≤ i := by
      by_contra! hij
      have hpow : (2 : ℝ) ^ i < 2 ^ j := pow_lt_pow_right₀ (by norm_num) hij
      have hdivlt : 1 / ((c : ℝ) * 2 ^ j) < 1 / ((c : ℝ) * 2 ^ i) :=
        div_lt_div_of_pos_left one_pos (by positivity) (mul_lt_mul_of_pos_left hpow hcR)
      linarith
    refine ⟨2 ^ (i - j), ?_⟩
    rw [hi, hj]
    push_cast
    have hp : (2 : ℝ) ^ i = 2 ^ (i - j) * 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    rw [hp]
    field_simp
    ring
  · exact htotal

private theorem score_unit_of_sum_ge_two {m : ℕ} (x : Fin m → ℝ) (hx : ∀ g, 0 ≤ x g)
    (R : Finset (Fin m)) (hR : 2 ≤ bundleValue (fun g => score (x g)) R) :
    ∃ B ⊆ R, bundleValue (fun g => score (x g)) B = 1 := by
  classical
  let w := fun g => score (x g)
  let family := fun g => ∃ j, w g = dyadic j
  let D := R.filter family
  let T := R.filter (fun g => 0 < w g ∧ ¬ family g)
  have hsum : bundleValue w D + bundleValue w T = bundleValue w R := by
    change (∑ g ∈ R.filter family, w g) +
      (∑ g ∈ R.filter (fun g => 0 < w g ∧ ¬ family g), w g) = _
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib, bundleValue]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hf : family g
    · simp [hf]
    · by_cases hp : 0 < w g
      · simp [hf, hp]
      · have hz : w g = 0 := le_antisymm (le_of_not_gt hp) (score_nonneg (hx g))
        simp [hf, hp, hz]
  by_cases hd : 1 ≤ bundleValue w D
  · obtain ⟨B, hB, hw⟩ := weighted_family_unit D w 1 (by decide) (fun g hg => by
      obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hg).2
      exact ⟨j, by simpa [dyadic] using hj⟩) hd
    exact ⟨B, hB.trans (Finset.filter_subset _ _), hw⟩
  · have ht : 1 ≤ bundleValue w T := by
      change 2 ≤ bundleValue w R at hR
      linarith
    obtain ⟨B, hB, hw⟩ := weighted_family_unit T w 3 (by decide) (fun g hg => by
      obtain ⟨hp, hnot⟩ := (Finset.mem_filter.mp hg).2
      rcases score_level (hx g) hp with hf | ⟨j, hj⟩
      · exact False.elim (hnot hf)
      · refine ⟨j, ?_⟩
        simpa [thirds, dyadic, div_div, mul_comm] using hj) ht
    exact ⟨B, hB.trans (Finset.filter_subset _ _), hw⟩

/-- A family of disjoint bundles with one unit of score each and the
required remaining own-type score after removal. -/
structure Candidates {m : ℕ} (w : Fin m → ℝ) (R : Finset (Fin m)) (r : ℕ) where
  bag : Fin r → Finset (Fin m)
  subset : ∀ j, bag j ⊆ R
  pays : ∀ j, 1 ≤ bundleValue w (bag j)
  leaves : ∀ j, (r : ℝ) - 1 ≤ bundleValue w (R \ bag j)
  disjoint : Pairwise (fun i j => Disjoint (bag i) (bag j))

private theorem sum_remove {m : ℕ} (w : Fin m → ℝ) {R B : Finset (Fin m)}
    (hB : B ⊆ R) : bundleValue w (R \ B) + bundleValue w B = bundleValue w R :=
  Finset.sum_sdiff hB

/-- The paper's two score families always allow packing the required number
of candidate bundles. Each unit bag is obtained by the divisibility of the
levels within its family. -/
theorem score_pack {m : ℕ} (x : Fin m → ℝ) (hx : ∀ g, 0 ≤ x g) :
    ∀ (r : ℕ) (R : Finset (Fin m)), (r : ℝ) ≤ bundleValue (fun g => score (x g)) R →
      Nonempty (Candidates (fun g => score (x g)) R r) := by
  let w := fun g => score (x g)
  intro r
  induction r with
  | zero =>
    intro R _
    exact ⟨⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0, fun i => i.elim0⟩⟩
  | succ r ih =>
    intro R hR
    by_cases hr : r = 0
    · subst r
      refine ⟨⟨fun _ => R, fun _ => Finset.Subset.rfl, fun _ => ?_, fun _ => ?_, ?_⟩⟩
      · simpa only [Nat.zero_add, Nat.cast_one] using hR
      · simp [bundleValue]
      · intro i j hij
        exact False.elim (hij (Fin.ext (by omega)))
    · have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      have htwo : 2 ≤ bundleValue w R := by
        change ((r + 1 : ℕ) : ℝ) ≤ bundleValue w R at hR
        push_cast at hR
        linarith
      obtain ⟨B, hB, hBpay⟩ := score_unit_of_sum_ge_two x hx R htwo
      have he := sum_remove w hB
      change bundleValue w B = 1 at hBpay
      have hh : (r : ℝ) ≤ bundleValue w (R \ B) := by
        change ((r + 1 : ℕ) : ℝ) ≤ bundleValue w R at hR
        push_cast at hR
        linarith
      obtain ⟨old⟩ := ih (R \ B) hh
      let bag : Fin (r + 1) → Finset (Fin m) := Fin.cons (α := fun _ => Finset (Fin m)) B old.bag
      have hsub (j : Fin (r + 1)) : bag j ⊆ R := by
        refine Fin.cases hB (fun i => ?_) j
        exact (old.subset i).trans Finset.sdiff_subset
      refine ⟨⟨bag, hsub, ?_, ?_, ?_⟩⟩
      · intro j
        refine Fin.cases hBpay.ge (fun i => ?_) j
        exact old.pays i
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · change ((r + 1 : ℕ) : ℝ) - 1 ≤ bundleValue w (R \ B)
          push_cast
          linarith
        · have hsmall := sum_remove w (old.subset i)
          have hlarge := sum_remove w (hsub i.succ)
          have hleave := old.leaves i
          change (r : ℝ) - 1 ≤ bundleValue w ((R \ B) \ old.bag i) at hleave
          change ((r + 1 : ℕ) : ℝ) - 1 ≤ bundleValue w (R \ old.bag i)
          change bundleValue w (R \ old.bag i) + bundleValue w (old.bag i) =
            bundleValue w R at hlarge
          push_cast
          linarith
      · intro i j hij
        have hdis (i : Fin r) : Disjoint B (old.bag i) :=
          (Finset.disjoint_left.mpr (fun g hg ho =>
            (Finset.mem_sdiff.mp (old.subset i ho)).2 hg))
        revert j
        refine Fin.cases (fun j hij => ?_) (fun i j hij => ?_) i
        · revert hij
          refine Fin.cases (fun hh => False.elim (hh rfl)) (fun j _ => hdis j) j
        · revert hij
          refine Fin.cases (fun _ => (hdis i).symm) (fun j hj => ?_) j
          exact old.disjoint (fun he => hj (congrArg Fin.succ he))

end OnlineMMS.TwoType
