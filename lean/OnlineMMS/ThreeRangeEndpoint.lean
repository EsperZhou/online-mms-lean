import OnlineMMS.ThreeRangeObstruction
import Mathlib.Data.Finset.Powerset

namespace OnlineMMS.ThreeRange

private noncomputable def scaledScore (x : ℝ) : ℝ :=
  if x < 3 then x else if x < 6 then 5 else 10

private theorem scaledScore_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ scaledScore x := by
  unfold scaledScore
  split_ifs <;> linarith

private theorem scaledScore_bound {x : ℝ} (hx : 0 ≤ x) : 3 * scaledScore x ≤ 5 * x := by
  unfold scaledScore
  split_ifs <;> linarith

private theorem scaledScore_eq (x : ℝ) :
    scaledScore (11 * x) = 10 * score (6 / 11) (11 / 10) x := by
  have h1 : 11 * x < 3 ↔ x < (6 / 11 : ℝ) / 2 := by constructor <;> intro h <;> linarith
  have h2 : 11 * x < 6 ↔ x < (6 / 11 : ℝ) := by constructor <;> intro h <;> linarith
  simp only [scaledScore, score, h1, h2]
  split_ifs <;> ring

private theorem score_sum_scaled {m : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m)) :
    bundleValue (fun g => scaledScore (11 * v g)) R =
      10 * bundleValue (fun g => score (6 / 11) (11 / 10) (v g)) R := by
  simp [bundleValue, scaledScore_eq, Finset.mul_sum]

private theorem value_sum_scaled {m : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m)) :
    bundleValue (fun g => 11 * v g) R = 11 * bundleValue v R := by simp [bundleValue, Finset.mul_sum]

private theorem sum_sdiff_add {m : ℕ} (w : Fin m → ℝ) {R B : Finset (Fin m)}
    (hB : B ⊆ R) : bundleValue w (R \ B) + bundleValue w B = bundleValue w R :=
  Finset.sum_sdiff hB

private theorem not_two_medium {m : ℕ} (x : Fin m → ℝ)
    {R : Finset (Fin m)}
    (h : ∀ B ⊆ R, bundleValue (fun g => scaledScore (x g)) B ≠ 10)
    (g : Fin m) (hg : g ∈ R) (hgm : 3 ≤ x g ∧ x g < 6)
    (j : Fin m) (hj : j ∈ R) (hjm : 3 ≤ x j ∧ x j < 6) : j = g := by
  by_contra hn
  have hne : g ≠ j := Ne.symm hn
  have hg' : g ∉ ({j} : Finset (Fin m)) := by simpa using hne
  apply h {g, j} (by simp [Finset.insert_subset_iff, hg, hj])
  rw [bundleValue, Finset.sum_insert hg', Finset.sum_singleton]
  norm_num [scaledScore, not_lt.mpr hgm.1, hgm.2, not_lt.mpr hjm.1, hjm.2]

/-- Value eleven is always enough for score ten in the rescaled endpoint. -/
private theorem scaled_initializes {m : ℕ} (x : Fin m → ℝ) (hx : ∀ g, 0 ≤ x g)
    (R : Finset (Fin m)) (hv : 11 ≤ bundleValue x R) :
    10 ≤ bundleValue (fun g => scaledScore (x g)) R := by
  classical
  let w := fun g => scaledScore (x g)
  by_contra! ht
  have hno : ∀ B ⊆ R, bundleValue w B ≠ 10 := by
    intro B hB he
    have hle : bundleValue w B ≤ bundleValue w R :=
      Finset.sum_le_sum_of_subset_of_nonneg hB (fun g _ _ => scaledScore_nonneg (hx g))
    linarith
  have hnoBig (g : Fin m) (hg : g ∈ R) : x g < 6 := by
    by_contra! hl
    exact hno {g} (Finset.singleton_subset_iff.mpr hg)
      (by simp [bundleValue, w, scaledScore, show ¬ x g < 3 by linarith, not_lt.mpr hl])
  by_cases hm : ∃ g ∈ R, 3 ≤ x g
  · obtain ⟨g, hg, hgm⟩ := hm
    have hall (i : Fin m) (hi : i ∈ R.erase g) : w i = x i := by
      obtain ⟨hne, hiR⟩ := Finset.mem_erase.mp hi
      have hs : x i < 3 := by
        by_contra! hh
        exact hne (not_two_medium x hno g hg ⟨hgm, hnoBig g hg⟩ i hiR ⟨hh, hnoBig i hiR⟩)
      simp [w, scaledScore, hs]
    have hs : bundleValue w (R.erase g) = bundleValue x (R.erase g) :=
      Finset.sum_congr rfl hall
    have hwg : w g = 5 := by simp [w, scaledScore, not_lt.mpr hgm, hnoBig g hg]
    have hxsum := Finset.sum_erase_add R x hg
    have hwsum := Finset.sum_erase_add R w hg
    change bundleValue x (R.erase g) + x g = bundleValue x R at hxsum
    change bundleValue w (R.erase g) + w g = bundleValue w R at hwsum
    linarith [hnoBig g hg]
  · have hs : bundleValue w R = bundleValue x R := by
      apply Finset.sum_congr rfl
      intro g hg
      have hl : x g < 3 := lt_of_not_ge (fun h => hm ⟨g, hg, h⟩)
      simp [w, scaledScore, hl]
    linarith

private theorem cons_disjoint {m r : ℕ} (C : Finset (Fin m))
    (B : Fin r → Finset (Fin m)) (hd : ∀ j, Disjoint C (B j))
    (hp : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Pairwise (fun i j => Disjoint (Fin.cons (α := fun _ => Finset (Fin m)) C B i) (Fin.cons (α := fun _ => Finset (Fin m)) C B j)) := by
  intro i j hij
  revert j
  refine Fin.cases (fun j hij => ?_) (fun i j hij => ?_) i
  · revert hij
    refine Fin.cases (fun hh => False.elim (hh rfl)) (fun j _ => hd j) j
  · revert hij
    refine Fin.cases (fun _ => (hd i).symm) (fun j hj => ?_) j
    exact hp (fun he => hj (congrArg Fin.succ he))

private theorem small_bundle {m : ℕ} (x : Fin m → ℝ) (R : Finset (Fin m))
    (hlight : ∀ g ∈ R, x g < 3) (htotal : 6 ≤ bundleValue x R) :
    ∃ B ⊆ R, 6 ≤ bundleValue x B ∧ bundleValue x B < 9 := by
  classical
  let pool := R.powerset.filter (fun B => 6 ≤ bundleValue x B)
  obtain ⟨B, hB, hmin⟩ := pool.exists_min_image Finset.card
    (⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, htotal⟩⟩)
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hpay := (Finset.mem_filter.mp hB).2
  have hne : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hpay
    norm_num [bundleValue] at hpay
  obtain ⟨g, hg⟩ := hne
  have hlt : bundleValue x (B.erase g) < 6 := by
    apply lt_of_not_ge
    intro hl
    have hh : B.erase g ∈ pool := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub), hl⟩
    exact (Nat.not_lt_of_ge (hmin _ hh)) (Finset.card_erase_lt_of_mem hg)
  have he := Finset.sum_erase_add B x hg
  change bundleValue x (B.erase g) + x g = bundleValue x B at he
  exact ⟨B, hsub, hpay, by linarith [hlight g (hsub hg)]⟩

private theorem pack_lights {m : ℕ} (x : Fin m → ℝ) :
    ∀ (r : ℕ) (R : Finset (Fin m)), (∀ g ∈ R, x g < 3) →
      9 * (r : ℝ) - 3 ≤ bundleValue x R →
      ∃ B : Fin r → Finset (Fin m), Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        ∀ j, B j ⊆ R ∧ 6 ≤ bundleValue x (B j) ∧ bundleValue x (B j) < 9 := by
  intro r
  induction r with
  | zero => intro R _ _; exact ⟨fun j => j.elim0, (fun j => j.elim0), fun j => j.elim0⟩
  | succ r ih =>
    intro R hlight htot
    push_cast at htot
    have hpay : 6 ≤ bundleValue x R := by linarith [Nat.cast_nonneg (α := ℝ) r]
    obtain ⟨C, hC, hCp, hCupper⟩ := small_bundle x R hlight hpay
    have hs := sum_sdiff_add x hC
    obtain ⟨B, hd, hb⟩ := ih (R \ C)
      (fun g hg => hlight g (Finset.mem_sdiff.mp hg).1) (by linarith)
    have hdis (j : Fin r) : Disjoint C (B j) := Finset.disjoint_left.mpr fun g hg hB =>
      (Finset.mem_sdiff.mp ((hb j).1 hB)).2 hg
    refine ⟨Fin.cons (α := fun _ => Finset (Fin m)) C B, cons_disjoint C B hdis hd, fun j => ?_⟩
    refine Fin.cases ⟨hC, hCp, hCupper⟩ (fun i => ?_) j
    exact ⟨(hb i).1.trans Finset.sdiff_subset, (hb i).2⟩

private theorem scaled_packs {m : ℕ} (x : Fin m → ℝ) (hx : ∀ g, 0 ≤ x g) :
    ∀ (r : ℕ) (R : Finset (Fin m)), 10 * (r : ℝ) ≤ bundleValue (fun g => scaledScore (x g)) R →
      ∃ B : Fin r → Finset (Fin m), Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        ∀ j, B j ⊆ R ∧ 6 ≤ bundleValue x (B j) ∧
          10 * ((r : ℝ) - 1) ≤ bundleValue (fun g => scaledScore (x g)) (R \ B j) := by
  classical
  let w := fun g => scaledScore (x g)
  intro r
  induction r with
  | zero => intro R _; exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ r ih =>
    intro R htot
    change 10 * ((r + 1 : ℕ) : ℝ) ≤ bundleValue w R at htot
    push_cast at htot
    by_cases hr : r = 0
    · subst r
      have hh : ∑ g ∈ R, 3 * w g ≤ ∑ g ∈ R, 5 * x g :=
        Finset.sum_le_sum fun g _ => scaledScore_bound (hx g)
      rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
      change 3 * bundleValue w R ≤ 5 * bundleValue x R at hh
      refine ⟨fun _ => R, (fun i j hij => False.elim (hij (Fin.ext (by omega)))), fun _ => ?_⟩
      refine ⟨Finset.Subset.rfl, by norm_num at htot; linarith, by simp [bundleValue]⟩
    · by_cases hunit : ∃ C ⊆ R, bundleValue w C = 10
      · obtain ⟨C, hC, hc⟩ := hunit
        have hh : ∑ g ∈ C, 3 * w g ≤ ∑ g ∈ C, 5 * x g :=
          Finset.sum_le_sum fun g _ => scaledScore_bound (hx g)
        rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
        change 3 * bundleValue w C ≤ 5 * bundleValue x C at hh
        have hs := sum_sdiff_add w hC
        obtain ⟨B, hdis, hB⟩ := ih (R \ C) (by linarith)
        have hdis' (j : Fin r) : Disjoint C (B j) :=
          Finset.disjoint_left.mpr fun g hg hgB => (Finset.mem_sdiff.mp ((hB j).1 hgB)).2 hg
        refine ⟨Fin.cons (α := fun _ => Finset (Fin m)) C B, cons_disjoint C B hdis' hdis, fun j => ?_⟩
        refine Fin.cases ?_ (fun i => ?_) j
        · refine ⟨hC, ?_, ?_⟩
          · change 6 ≤ bundleValue x C
            linarith
          change 10 * (((r + 1 : ℕ) : ℝ) - 1) ≤ bundleValue w (R \ C)
          push_cast
          linarith
        · obtain ⟨hBi, hp, hleft⟩ := hB i
          have hsub := hBi.trans (Finset.sdiff_subset : R \ C ⊆ R)
          refine ⟨hsub, hp, ?_⟩
          have hh' := sum_sdiff_add w hBi
          have hh'' := sum_sdiff_add w hsub
          change 10 * (((r + 1 : ℕ) : ℝ) - 1) ≤ bundleValue w (R \ B i)
          change 10 * ((r : ℝ) - 1) ≤ bundleValue w ((R \ C) \ B i) at hleft
          push_cast
          linarith
      · have hnone : ∀ B ⊆ R, bundleValue w B ≠ 10 := fun B hB h => hunit ⟨B, hB, h⟩
        have hbig (g : Fin m) (hg : g ∈ R) : x g < 6 := by
          apply lt_of_not_ge
          intro hl
          have hn3 : ¬ x g < 3 := by linarith
          exact hnone {g} (Finset.singleton_subset_iff.mpr hg)
            (by simp [bundleValue, w, scaledScore, hn3, not_lt.mpr hl])
        let light := R.filter (fun g => x g < 3)
        have hlights (g : Fin m) (hg : g ∈ light) : x g < 3 := (Finset.mem_filter.mp hg).2
        have hL : bundleValue x light = bundleValue w light := by
          apply Finset.sum_congr rfl
          exact fun g hg => by simp [w, scaledScore, hlights g hg]
        have hleft := sum_sdiff_add w (show light ⊆ R from Finset.filter_subset _ _)
        have hmedium : bundleValue w (R \ light) ≤ 5 := by
          by_cases hne : (R \ light).Nonempty
          · obtain ⟨g, hg⟩ := hne
            have hmember (j : Fin m) (hj : j ∈ R \ light) : j ∈ R ∧ 3 ≤ x j ∧ x j < 6 := by
              obtain ⟨hjR, hjL⟩ := Finset.mem_sdiff.mp hj
              exact ⟨hjR, le_of_not_gt (fun h => hjL (Finset.mem_filter.mpr ⟨hjR, h⟩)), hbig j hjR⟩
            have heq : R \ light = {g} := by
              ext j
              refine ⟨fun hj => Finset.mem_singleton.mpr (not_two_medium x hnone g
                (hmember g hg).1 (hmember g hg).2 j (hmember j hj).1 (hmember j hj).2), ?_⟩
              intro hj
              rwa [Finset.mem_singleton.mp hj]
            rw [heq]
            simp [bundleValue, w, scaledScore, not_lt.mpr (hmember g hg).2.1, (hmember g hg).2.2]
          · simp [Finset.not_nonempty_iff_eq_empty.mp hne, bundleValue]
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
        obtain ⟨B, hdis, hB⟩ := pack_lights x (r + 1) light hlights (by
          push_cast
          linarith)
        refine ⟨B, hdis, fun j => ?_⟩
        obtain ⟨hsub, hpay, hcost⟩ := hB j
        have hh : B j ⊆ R := hsub.trans (Finset.filter_subset _ _)
        have hsplit := sum_sdiff_add w hh
        have hcost' : bundleValue w (B j) = bundleValue x (B j) := by
          apply Finset.sum_congr rfl
          exact fun g hg => by simp [w, scaledScore, hlights g (hsub hg)]
        refine ⟨hh, hpay, ?_⟩
        change 10 * (((r + 1 : ℕ) : ℝ) - 1) ≤ bundleValue w (R \ B j)
        push_cast
        linarith

/-- The endpoint certifies both requirements at target 6/11. -/
theorem three_range_endpoint : Initializes (6 / 11) (11 / 10) ∧ Packs (6 / 11) (11 / 10) := by
  constructor
  · intro m v hv R hR
    have hs := scaled_initializes (fun g => 11 * v g) (fun g => mul_nonneg (by norm_num) (hv g)) R
      (by rw [value_sum_scaled]; linarith)
    rw [score_sum_scaled] at hs
    linarith
  · intro m v hv r R hR
    obtain ⟨B, hd, hB⟩ := scaled_packs (fun g => 11 * v g)
      (fun g => mul_nonneg (by norm_num) (hv g)) r R (by rw [score_sum_scaled]; linarith)
    refine ⟨B, hd, fun j => ?_⟩
    obtain ⟨hsub, hpay, hleft⟩ := hB j
    rw [value_sum_scaled] at hpay
    rw [score_sum_scaled] at hleft
    exact ⟨hsub, by linarith, by linarith⟩

end OnlineMMS.ThreeRange
