import OnlineMMS.General

namespace OnlineMMS.FixedWidth

/-- Remaining goods, current weights, sample count, and an estimator payload. -/
structure State (m k : ℕ) (σ : Type) where
  remaining : Finset (Fin m)
  samples : ℕ
  weight : Fin k → Fin m → ℝ
  stats : σ

def total {m k : ℕ} {σ : Type} (x : State m k σ) (t : Fin k) : ℝ :=
  bundleValue (x.weight t) x.remaining

def deficit {m k : ℕ} {σ : Type} (x : State m k σ) (r : ℕ) (t : Fin k) : ℝ :=
  (r : ℝ) + x.samples - total x t

structure Valid {m k : ℕ} {σ : Type} (v : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (x : State m k σ) : Prop where
  weights : ∀ t g, 0 ≤ x.weight t g ∧ x.weight t g ≤ 1
  value : ∀ t g, d t * x.weight t g ≤ v t g
  cap : ∀ t, total x t ≤ (r : ℝ) + x.samples
  exactBefore : x.samples = 0 → ∀ t, 0 < d t → total x t = r

noncomputable def init {m k : ℕ} {σ : Type} (v : Fin k → Fin m → ℝ) (n : ℕ) (stats : σ) :
    State m k σ := ⟨Finset.univ, 0, fun t => normalizedWeight (v t) n, stats⟩

theorem valid_init {m k n : ℕ} {σ : Type} (hn : 0 < n) (v : Fin k → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (stats : σ) :
    Valid v (fun t => truncatedShare (v t) n) n (init v n stats) := by
  have hzero (t : Fin k) (ht : ¬0 < truncatedShare (v t) n) (g : Fin m) :
      normalizedWeight (v t) n g = 0 := by
    have hs := (truncatedShare_spec (v t) (hv t) hn).1.1
    have hz := le_antisymm (le_of_not_gt ht) hs
    simp [normalizedWeight, hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t g
    by_cases h : 0 < truncatedShare (v t) n
    · exact ⟨normalizedWeight_nonneg (v t) (hv t) h g, normalizedWeight_le_one (v t) h g⟩
    · change 0 ≤ normalizedWeight (v t) n g ∧ normalizedWeight (v t) n g ≤ 1
      rw [hzero t h g]
      norm_num
  · intro t g
    by_cases h : 0 < truncatedShare (v t) n
    · exact truncatedShare_mul_normalizedWeight_le (v t) h g
    · change truncatedShare (v t) n * normalizedWeight (v t) n g ≤ v t g
      simpa [hzero t h] using hv t g
  · intro t
    by_cases h : 0 < truncatedShare (v t) n
    · have he := sum_normalizedWeight (v t) (hv t) hn h
      simpa [init, total, bundleValue] using he.le
    · simp [init, total, bundleValue, hzero t h]
  · intro _ t ht
    exact sum_normalizedWeight (v t) (hv t) hn ht

noncomputable def afterSmall {m k : ℕ} {σ : Type} (r : ℕ) (x : State m k σ)
    (B : Finset (Fin m)) : State m k σ :=
  ⟨x.remaining \ B, x.samples, fun t =>
    trimWeights (x.remaining \ B) (x.weight t) ((r : ℝ) + x.samples), x.stats⟩

def afterSample {m k : ℕ} {σ : Type} (x : State m k σ) (gs : List (Fin m))
    (data : σ) : State m k σ :=
  ⟨x.remaining \ gs.toFinset, x.samples + 1, x.weight, data⟩

theorem small_valid {m k r : ℕ} {σ : Type} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : State m k σ} (hx : Valid v d (r + 1) x)
    (hd : ∀ t, 0 ≤ d t) {B : Finset (Fin m)} (hsub : B ⊆ x.remaining)
    (hsmall : ∀ t, bundleValue (x.weight t) B ≤ 1) :
    Valid v d r (afterSmall r x B) ∧
      ∀ t, deficit (afterSmall r x B) r t ≤ deficit x (r + 1) t := by
  let y := afterSmall r x B
  let cap := (r : ℝ) + x.samples
  have trim (t : Fin k) := trimWeights_spec (x.remaining \ B) (x.weight t)
    (fun g => (hx.weights t g).1) cap (by dsimp [cap]; linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) x.samples])
  have htotal (t : Fin k) :
      total y t = min (total x t - bundleValue (x.weight t) B) cap := by
    have he : bundleValue (x.weight t) (x.remaining \ B) =
        total x t - bundleValue (x.weight t) B := by
      have hs := Finset.sum_sdiff hsub (f := x.weight t)
      change bundleValue (x.weight t) (x.remaining \ B) + bundleValue (x.weight t) B =
        total x t at hs
      linarith
    exact (trim t).2.trans (congrArg (fun z => min z cap) he)
  have hb (t : Fin k) : total y t ≤ cap ∧ deficit y r t ≤ deficit x (r + 1) t := by
    have he : (((r + 1 : ℕ) : ℝ) + x.samples) = cap + 1 := by
      dsimp [cap]
      push_cast
      ring
    have hl : bundleValue (x.weight t) B ≤ total x t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => (hx.weights t g).1)
    have hh := trim_reserve (N := cap + 1) (by dsimp [cap]; linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) x.samples])
      (he ▸ hx.cap t) hl (hsmall t)
    rw [deficit, deficit, htotal, he]
    change min (total x t - bundleValue (x.weight t) B) cap ≤ cap ∧
      cap - min (total x t - bundleValue (x.weight t) B) cap ≤ cap + 1 - total x t
    simpa only [add_sub_cancel_right] using hh.2
  refine ⟨⟨?_, ?_, fun t => (hb t).1, ?_⟩, fun t => (hb t).2⟩
  · intro t g
    exact ⟨((trim t).1 g).1, ((trim t).1 g).2.trans (hx.weights t g).2⟩
  · intro t g
    exact (mul_le_mul_of_nonneg_left ((trim t).1 g).2 (hd t)).trans (hx.value t g)
  · intro hs t ht
    change x.samples = 0 at hs
    obtain ⟨hu, hl⟩ := hb t
    change total y t ≤ (r : ℝ) + x.samples at hu
    change (r : ℝ) + x.samples - total y t ≤
      ((r + 1 : ℕ) : ℝ) + x.samples - total x t at hl
    rw [hx.exactBefore hs t ht] at hl
    simp [hs] at hu hl
    exact le_antisymm hu hl

theorem weight_list_sum {m : ℕ} (w : Fin m → ℝ) (gs : List (Fin m)) (hnd : gs.Nodup) :
    (gs.map w).sum = bundleValue w gs.toFinset := by
  induction gs with
  | nil => simp [bundleValue]
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := List.nodup_cons.mp hnd
    have hnot : g ∉ gs.toFinset := by simpa using hg
    simp [bundleValue, Finset.sum_insert hnot, ih hgs]

theorem sample_valid {m k r : ℕ} {σ : Type} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : State m k σ} (hx : Valid v d (r + 1) x)
    {gs : List (Fin m)} (hsub : gs.toFinset ⊆ x.remaining) (hnd : gs.Nodup) (data : σ) :
    Valid v d r (afterSample x gs data) ∧
      ∀ t, deficit (afterSample x gs data) r t = deficit x (r + 1) t +
        (gs.map (x.weight t)).sum := by
  have he (t : Fin k) : deficit (afterSample x gs data) r t = deficit x (r + 1) t +
      (gs.map (x.weight t)).sum := by
    have hz := Finset.sum_sdiff hsub (f := x.weight t)
    rw [weight_list_sum _ _ hnd]
    unfold deficit total afterSample bundleValue
    push_cast
    linarith
  refine ⟨⟨hx.weights, hx.value, ?_, ?_⟩, he⟩
  · intro t
    have hbefore := hx.cap t
    have hsum : 0 ≤ (gs.map (x.weight t)).sum := List.sum_nonneg (by
      intro x' hx'
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx'
      exact (hx.weights t g).1)
    have hh := he t
    simp only [deficit, afterSample, Nat.cast_succ, Nat.cast_add, Nat.cast_one] at hh hbefore ⊢
    linarith
  · change x.samples + 1 = 0 → _
    omega

private theorem valued {m k : ℕ} {σ : Type} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : State m k σ} {t : Fin k} {B : Finset (Fin m)} {β : ℝ}
    (hd : 0 ≤ d t) (hw : ∀ g, d t * x.weight t g ≤ v t g)
    (hpay : β ≤ bundleValue (x.weight t) B) : d t * β ≤ bundleValue (v t) B := by
  calc
    _ ≤ d t * bundleValue (x.weight t) B := mul_le_mul_of_nonneg_left hpay hd
    _ = ∑ g ∈ B, d t * x.weight t g := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun g _ => hw g)

/-- Any estimator satisfying the stated per-sample and reserve obligations
drives the fixed-width online rule, including trimming and singleton rounds. -/
theorem policy_from_estimator {m k n : ℕ} {σ : Type} (hn : 0 < n)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (h : ℕ) (hh : 0 < h) (β : ℝ) (hβ : 0 ≤ β)
    (initial : σ) (inv : ℕ → State m k σ → Prop)
    (hinit : inv n (init v n initial))
    (htrim : ∀ r x, Valid v (fun t => truncatedShare (v t) n) (r + 1) x →
      inv (r + 1) x → ∀ B ⊆ x.remaining, (∀ t, bundleValue (x.weight t) B ≤ 1) →
      inv r (afterSmall r x B))
    (hchoose : ∀ r x, Valid v (fun t => truncatedShare (v t) n) (r + 1) x →
      inv (r + 1) x → ∀ t : Fin k, ∀ buckets,
      SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets →
      ∃ gs data, List.Forall₂ (fun C g => g ∈ C) buckets gs ∧ inv r (afterSample x gs data))
    (hnonfinal : ∀ r x, r ≠ 0 → Valid v (fun t => truncatedShare (v t) n) (r + 1) x →
      inv (r + 1) x → ∀ t, 0 < truncatedShare (v t) n →
      2 * β * ((h * (r + 1 + x.samples) : ℕ) : ℝ) ≤ total x t)
    (hfinal : ∀ x, Valid v (fun t => truncatedShare (v t) n) 1 x →
      inv 1 x → ∀ t, 0 < truncatedShare (v t) n → β ≤ total x t) :
    ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => truncatedShare (v t) n * β) Finset.univ := by
  classical
  let d : Fin k → ℝ := fun t => truncatedShare (v t) n
  have hd (t : Fin k) : 0 ≤ d t := (truncatedShare_spec (v t) (hv t) hn).1.1
  let valid (r : ℕ) (x : State m k σ) : Prop := r = 0 ∨ (Valid v d r x ∧ inv r x)
  have hi : valid n (init v n initial) := Or.inr ⟨valid_init hn v hv initial, hinit⟩
  exact policy_of_steps State.remaining valid v (fun t => d t * β) (by
    intro r x hx t
    rcases hx with hz | ⟨hx, hInv⟩
    · omega
    have hsmall (B : Finset (Fin m)) (hsub : B ⊆ x.remaining)
        (hB : ∀ i, bundleValue (x.weight i) B ≤ 1)
        (hpay : d t * β ≤ bundleValue (v t) B) :
        ∃ G y, G ⊆ x.remaining ∧ d t * β ≤ bundleValue (v t) G ∧
          y.remaining = x.remaining \ G ∧ valid r y :=
      ⟨B, afterSmall r x B, hsub, hpay, rfl,
        Or.inr ⟨(small_valid hx hd hsub hB).1, htrim r x hx hInv B hsub hB⟩⟩
    by_cases hr : r = 0
    · subst r
      refine ⟨x.remaining, ⟨∅, x.samples, x.weight, x.stats⟩, Finset.Subset.rfl, ?_, by simp, Or.inl rfl⟩
      by_cases ht : 0 < d t
      · exact valued ht.le (hx.value t) (hfinal _ hx hInv _ ht)
      · change d t * β ≤ bundleValue (v t) x.remaining
        rw [le_antisymm (le_of_not_gt ht) (hd t), zero_mul]
        exact Finset.sum_nonneg fun g _ => hv t g
    by_cases ht : 0 < d t
    · by_cases hsingle : ∃ g ∈ x.remaining, β ≤ x.weight t g
      · obtain ⟨g, hg, hpay⟩ := hsingle
        exact hsmall {g} (Finset.singleton_subset_iff.mpr hg)
          (fun i => by simpa [bundleValue] using (hx.weights i g).2)
          (valued ht.le (hx.value t) (by simpa [bundleValue] using hpay))
      · let H := h * (r + 1 + x.samples)
        have hH : 0 < H := Nat.mul_pos hh (by omega)
        obtain ⟨buckets, hb⟩ := SortedBuckets.exists_buckets (w := x.weight t) hH x.remaining
        obtain ⟨gs, data, hg, hs⟩ := hchoose r x hx hInv t buckets hb
        obtain ⟨hsub, hnd⟩ := hb.selected_valid hg
        have hpre := hnonfinal r x hr hx hInv t ht
        have hsorted := hb.payment hg (fun g => (hx.weights t g).1) hβ
          (fun g hg => le_of_lt (lt_of_not_ge (fun h => hsingle ⟨g, hg, h⟩)))
        have hsorted' : (2 * β) * (H : ℝ) ≤
            (H : ℝ) * (β + (gs.map (x.weight t)).sum) := hpre.trans hsorted
        have hpay : β ≤ (gs.map (x.weight t)).sum := by
          have hpos : (0 : ℝ) < H := by exact_mod_cast hH
          have he : (2 * β) * (H : ℝ) = (H : ℝ) * (2 * β) := mul_comm _ _
          rw [he] at hsorted'
          have h := (mul_le_mul_left hpos).mp hsorted'
          linarith
        rw [weight_list_sum _ _ hnd] at hpay
        exact ⟨_, _, hsub, valued ht.le (hx.value t) hpay, rfl,
          Or.inr ⟨(sample_valid hx hsub hnd data).1, hs⟩⟩
    · have hz : d t = 0 := le_antisymm (le_of_not_gt ht) (hd t)
      exact hsmall ∅ (Finset.empty_subset _) (fun _ => by simp [bundleValue]) (by simp [hz, bundleValue])
    ) n (init v n initial) hi

end OnlineMMS.FixedWidth
