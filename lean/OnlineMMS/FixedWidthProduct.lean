import OnlineMMS.FixedWidthKernel
import OnlineMMS.BucketBitComplexity
import OnlineMMS.Asymptotic

namespace OnlineMMS.FixedWidth

noncomputable def productMultiplier (k : ℕ) : ℕ :=
  max 4 (Nat.ceil (2 * Real.sqrt (k : ℝ)))

theorem productMultiplier_bounds (k : ℕ) :
    4 ≤ productMultiplier k ∧ (k : ℝ) ≤ (productMultiplier k : ℝ) ^ 2 / 4 := by
  have h₁ : 4 ≤ productMultiplier k := le_max_left _ _
  have h₂ : 2 * Real.sqrt (k : ℝ) ≤ (productMultiplier k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 4 (Nat.ceil (2 * Real.sqrt (k : ℝ)))))
  have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hpow := pow_le_pow_left₀ (show 0 ≤ 2 * Real.sqrt (k : ℝ) by positivity) h₂ 2
  refine ⟨h₁, ?_⟩
  nlinarith only [hs, hpow]

private noncomputable def growth (h : ℝ) : ℝ := 3 - 2 / h

private theorem growth_nonneg {h : ℝ} (hh : 4 ≤ h) : 0 < growth h := by
  have hb : (2 : ℝ) / h ≤ 1 := (div_le_one₀ (by linarith)).mpr (by linarith)
  unfold growth
  linarith

private theorem growth_lt_three {h : ℝ} (hh : 4 ≤ h) : growth h < 3 := by
  unfold growth
  have : 0 < (2 : ℝ) / h := by positivity
  linarith

private theorem growth_cube {h : ℕ} (hh : 4 ≤ h) :
    growth (h : ℝ) ^ 3 ≤ (h : ℝ) ^ 2 := by
  by_cases hsmall : h < 6
  · interval_cases h <;> norm_num [growth]
  · have hhR : (4 : ℝ) ≤ h := by exact_mod_cast hh
    have h6 : (6 : ℝ) ≤ h := by exact_mod_cast (show 6 ≤ h by omega)
    have hp := pow_le_pow_left₀ (growth_nonneg hhR).le (growth_lt_three hhR).le 3
    nlinarith only [hp, h6, sq_nonneg ((h : ℝ) - 6)]

private theorem exp_mean_le_growth {h z : ℝ} (hh : 4 ≤ h)
    (_hz0 : 0 ≤ z) (hz : z ≤ 1 / h) :
    Real.exp ((h - 1) * z) ≤ growth h := by
  have hh0 : 0 < h := by linarith
  have hrec : (h - 1) * (1 / h) = 1 - 1 / h := by field_simp
  have ha : 0 ≤ 1 - 1 / h := sub_nonneg.mpr ((div_le_one₀ hh0).mpr (by linarith))
  have hb : 0 ≤ 1 / h := by positivity
  have hchord := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from trivial)
    (show (1 : ℝ) ∈ Set.univ from trivial) hb ha (show 1 / h + (1 - 1 / h) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hchord
  have hE : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hm := mul_le_mul_of_nonneg_left hE ha
  calc
    _ ≤ Real.exp (1 - 1 / h) := by
      apply Real.exp_le_exp.mpr
      rw [← hrec]
      exact mul_le_mul_of_nonneg_left hz (by linarith)
    _ ≤ (1 / h) + (1 - 1 / h) * Real.exp 1 := hchord
    _ ≤ (1 / h) + (1 - 1 / h) * 3 := add_le_add_left hm _
    _ = growth h := by unfold growth; ring

private theorem product_deficit_bound {h k s : ℕ} (hh : 4 ≤ h) (_hk : 0 < k)
    (hcap : (k : ℝ) ≤ (h : ℝ)^2 / 4) (hs : 0 < s) (D : ℝ)
    (hp : (h : ℝ) ^ D ≤ (k : ℝ) * growth (h : ℝ) ^ s) :
    D ≤ 2 - 1 / (6 * (h : ℝ)) + (2 / 3 : ℝ) * ((s : ℝ) - 1) := by
  let H : ℝ := h
  let c := growth H
  have h4 : 4 ≤ H := by
    change (4 : ℝ) ≤ (h : ℝ)
    exact_mod_cast hh
  have hH0 : 0 < H := by linarith
  have hlog0 : 0 < Real.log H := Real.log_pos (by linarith)
  have hc0 : 0 < c := growth_nonneg h4
  have hkc : (k : ℝ) * c ≤ (3 / 4 : ℝ) * H ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hcap hc0.le
    have h2 := mul_le_mul_of_nonneg_left (growth_lt_three h4).le
      (show 0 ≤ H ^ 2 / 4 by positivity)
    change (k : ℝ) * c ≤ (3 / 4 : ℝ) * H ^ 2
    calc
      _ ≤ H ^ 2 / 4 * c := h1
      _ ≤ H ^ 2 / 4 * 3 := h2
      _ = _ := by ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  change H ^ D ≤ (k : ℝ) * c ^ (j + 1) at hp
  rw [pow_succ, mul_comm (c ^ j) c] at hp
  have hp' : H ^ D ≤ (3 / 4 : ℝ) * H ^ 2 * c ^ j := by
    have hstep := mul_le_mul_of_nonneg_right hkc (pow_nonneg hc0.le j)
    apply le_trans hp
    simpa only [mul_assoc] using hstep
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hH0 D) hp'
  rw [Real.log_rpow hH0, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hgap := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
  have hcPow := Real.log_le_log (pow_pos hc0 3) (growth_cube hh)
  change Real.log (c ^ (3 : ℕ)) ≤ Real.log (H ^ (2 : ℕ)) at hcPow
  rw [Real.log_pow, Real.log_pow] at hcPow
  norm_num at hcPow hlog
  have hrate : Real.log c ≤ 2 / 3 * Real.log H := by linarith
  have hstep := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg j)
  have hβlog : (1 / (6 * H)) * Real.log H ≤ 1 / 4 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (show 0 < (6 : ℝ) * H by positivity)).mpr
    linarith [Real.log_le_sub_one_of_pos hH0]
  change D ≤ 2 - 1 / (6 * H) + (2 / 3 : ℝ) * (((j + 1 : ℕ) : ℝ) - 1)
  push_cast
  apply (mul_le_mul_right hlog0).mp
  nlinarith only [hlog, hstep, hgap, hβlog]

def ProductInv {m k : ℕ} (h : ℝ) (d : Fin k → ℝ) (r : ℕ)
    (x : State m k (Fin k → ℝ)) : Prop :=
  (∀ t, 0 ≤ x.stats t) ∧
  (∀ t, 0 < d t → h ^ deficit x r t ≤ x.stats t) ∧
  (∑ t, x.stats t) ≤ (k : ℝ) * growth h ^ x.samples

theorem product_sample_preserves {m n k r h : ℕ} (hh : 4 ≤ h)
    {v : Fin k → Fin m → ℝ} {x : State m k (Fin k → ℝ)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets)
    (gs : List (Fin m)) (hg : List.Forall₂ (fun C g => g ∈ C) buckets gs)
    (hobj : sampleObjective (h : ℝ) 0 1 x.stats (gs.map (fun g i => x.weight i g)) ≤
      sampleObjective (h : ℝ) 0 1 x.stats (slotMeans x.weight buckets)) :
    ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) r
      (afterSample x gs (fun i => x.stats i * sampleProduct (h : ℝ) (gs.map (x.weight i)))) := by
  classical
  let H := h * (r + 1 + x.samples)
  let N : ℝ := ((r + 1 : ℕ) : ℝ) + x.samples
  have hH : 0 < H := Nat.mul_pos (by omega) (by omega)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hhR : (4 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hN : 0 < N := by dsimp [N]; push_cast; positivity
  obtain ⟨hsub, hnd⟩ := hb.selected_valid hg
  let data := fun i => x.stats i * sampleProduct (h : ℝ) (gs.map (x.weight i))
  let means := slotMeans x.weight buckets
  have hmass (i : Fin k) : (means.map (fun w => w i)).sum ≤ 1 / (h : ℝ) := by
    have hh := slotMeans_sum_le_of_width x.weight buckets x.remaining H hb.pairwise_disjoint
      hb.bucket_size hb.bucket_subsets i (fun g => (hx.weights i g).1)
    refine hh.trans (le_trans (div_le_div_of_nonneg_right (hx.cap i) hH'.le) ?_)
    have he : (H : ℝ) = (h : ℝ) * N := by dsimp [H, N]; push_cast; rfl
    change N / (H : ℝ) ≤ _
    rw [he]
    have heq : N / ((h : ℝ) * N) = 1 / (h : ℝ) := by
      field_simp [hN.ne', hh0.ne']
      ring
    exact heq.le
  have hmean : sampleObjective (h : ℝ) 0 1 x.stats means ≤ (∑ i, x.stats i) * growth h := by
    unfold sampleObjective
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    let row := means.map (fun z => z i)
    have hxrow : ∀ x' ∈ row, 0 ≤ x' :=
      slotMeans_nonneg x.weight buckets i (fun g => (hx.weights i g).1)
    have hp := (sampleProduct_le_exp (by linarith : (1 : ℝ) ≤ h) row hxrow).trans
      (exp_mean_le_growth hhR (List.sum_nonneg hxrow) (hmass i))
    simpa only [rowObjective, zero_mul, one_mul, zero_add] using
      mul_le_mul_of_nonneg_left hp (hi.1 i)
  have hd := (sample_valid hx hsub hnd data).2
  have hxs (i : Fin k) : ∀ z ∈ gs.map (x.weight i), 0 ≤ z ∧ z ≤ 1 := by
    intro z hz
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hz
    exact hx.weights i g
  change ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) r (afterSample x gs data)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg (hi.1 i) (sampleProduct_nonneg (by linarith : (1 : ℝ) ≤ h) _
      (fun z hz => (hxs i z hz).1))
  · intro i ht
    rw [hd i]
    exact rpow_deficit_add_le (by linarith : (1 : ℝ) ≤ h) _ (hxs i) (hi.2.1 i ht)
  · change (∑ i, data i) ≤ (k : ℝ) * growth h ^ (x.samples + 1)
    have hA : (∑ i, data i) ≤ (∑ i, x.stats i) * growth h := by
      simpa [data, sampleObjective, rowObjective, List.map_map, Function.comp_def] using hobj.trans hmean
    rw [pow_succ, ← mul_assoc]
    exact hA.trans (mul_le_mul_of_nonneg_right hi.2.2 (growth_nonneg hhR).le)

private theorem product_choose {m n k r h : ℕ} (hh : 4 ≤ h)
    {v : Fin k → Fin m → ℝ} {x : State m k (Fin k → ℝ)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets) :
    ∃ gs data, List.Forall₂ (fun C g => g ∈ C) buckets gs ∧
      ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) r (afterSample x gs data) := by
  have hH : 0 < h * (r + 1 + x.samples) := Nat.mul_pos (by omega) (by omega)
  have hnonempty (C : Finset (Fin m)) (hC : C ∈ buckets) : C.Nonempty :=
    Finset.card_pos.mp (hb.bucket_size C hC ▸ hH)
  obtain ⟨gs, hg, hobj⟩ := exists_sample_le_mean x.weight (h : ℝ) 0 1 x.stats buckets hnonempty
  exact ⟨gs, _, hg, product_sample_preserves hh hx hi t buckets hb gs hg hobj⟩

/-- The executable rational selector preserves the product
invariant whenever its rational state represents the current real state. -/
theorem product_rational_sample_preserves {m n k r h : ℕ} (hh : 4 ≤ h)
    {v : Fin k → Fin m → ℝ} {x : State m k (Fin k → ℝ)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (w : Fin k → Fin m → ℚ) (P : Fin k → ℚ)
    (hw : ∀ i g, (w i g : ℝ) = x.weight i g) (hP : ∀ i, (P i : ℝ) = x.stats i)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets) :
    let gs := BucketBitComplexity.selectQ w (h : ℚ) 0 1 P [] buckets
    List.Forall₂ (fun C g => g ∈ C) buckets gs ∧
      ProductInv (h : ℝ) (fun t => truncatedShare (v t) n) r
        (afterSample x gs (fun i => x.stats i * sampleProduct (h : ℝ) (gs.map (x.weight i)))) := by
  have hH : 0 < h * (r + 1 + x.samples) := Nat.mul_pos (by omega) (by omega)
  have hnonempty (C : Finset (Fin m)) (hC : C ∈ buckets) : C.Nonempty :=
    Finset.card_pos.mp (hb.bucket_size C hC ▸ hH)
  let gs := BucketBitComplexity.selectQ w (h : ℚ) 0 1 P [] buckets
  obtain ⟨hg, hq⟩ := BucketBitComplexity.selectQ_objective_le w (h : ℚ) 0 1 P buckets hnonempty
  change List.Forall₂ (fun C g => g ∈ C) buckets gs ∧ _
  refine ⟨hg, product_sample_preserves hh hx hi t buckets hb gs hg ?_⟩
  have hr : (BucketBitComplexity.objectiveQ (h : ℚ) 0 1 P
      (gs.map (fun g i => w i g)) : ℝ) ≤
      (BucketBitComplexity.objectiveQ (h : ℚ) 0 1 P
        (BucketBitComplexity.slotMeansQ w buckets) : ℝ) := by exact_mod_cast hq
  rw [BucketBitComplexity.objectiveQ_cast, BucketBitComplexity.objectiveQ_cast,
    BucketBitComplexity.slotMeansQ_cast] at hr
  have hwf : (fun i g => (w i g : ℝ)) = x.weight := by funext i g; exact hw i g
  have hPf : (fun i => (P i : ℝ)) = x.stats := by funext i; exact hP i
  simpa [BucketBitComplexity.realProfiles, List.map_map, Function.comp_def, hw, hwf, hPf] using hr

def productUpdateQ {m k : ℕ} (h : ℕ) (P : Fin k → ℚ) (w : Fin k → Fin m → ℚ)
    (gs : List (Fin m)) (i : Fin k) : ℚ :=
  P i * BucketBitComplexity.sampleProductQ (h : ℚ) (gs.map (w i))

theorem productUpdateQ_cast {m k : ℕ} (h : ℕ) (P : Fin k → ℚ)
    (w : Fin k → Fin m → ℚ) (gs : List (Fin m))
    (realP : Fin k → ℝ) (realW : Fin k → Fin m → ℝ)
    (hP : ∀ i, (P i : ℝ) = realP i) (hw : ∀ i g, (w i g : ℝ) = realW i g) (i : Fin k) :
    (productUpdateQ h P w gs i : ℝ) =
      realP i * sampleProduct (h : ℝ) (gs.map (realW i)) := by
  simp [productUpdateQ, BucketBitComplexity.sampleProductQ_cast, List.map_map,
    Function.comp_def, hP, hw]

/-- The fixed-width product estimator guarantees the stated fraction of original TPS. -/
theorem fixed_width_product_guarantee {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n, policy.Guarantees v
      (fun t => truncatedShare (v t) n / (6 * (productMultiplier k : ℝ))) Finset.univ := by
  let h := productMultiplier k
  let β : ℝ := 1 / (6 * (h : ℝ))
  let d : Fin k → ℝ := fun t => truncatedShare (v t) n
  obtain ⟨hh, hcap⟩ := productMultiplier_bounds k
  change 4 ≤ h at hh
  have hhR : (4 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hd (t : Fin k) : 0 ≤ d t := (truncatedShare_spec (v t) (hv t) hn).1.1
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβle : β ≤ 1 := by
    dsimp [β]
    apply (div_le_one₀ (show 0 < (6 : ℝ) * h by positivity)).mpr
    linarith
  have hreserve : ∀ r (x : State m k (Fin k → ℝ)), Valid v d r x → ProductInv (h : ℝ) d r x →
      ∀ t, 0 < d t → 0 < x.samples →
      deficit x r t ≤ 2 - β + (2 / 3 : ℝ) * ((x.samples : ℝ) - 1) := by
    intro r x hx hi t ht hs
    have h := (hi.2.1 t ht).trans <| (Finset.single_le_sum
      (fun i _ => hi.1 i) (Finset.mem_univ t)).trans hi.2.2
    exact product_deficit_bound hh hk hcap hs _ h
  suffices hpolicy : ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => d t * β) Finset.univ by
    simpa [β, h, d, div_eq_mul_inv] using hpolicy
  refine policy_from_estimator hn v hv h (by omega) β hβ (fun _ : Fin k => (1 : ℝ))
    (ProductInv (h : ℝ) d) ?_ ?_ (fun r x hx hi => product_choose hh hx hi) ?_ ?_
  · refine ⟨fun _ => zero_le_one, ?_, ?_⟩
    · intro t ht
      have hval := sum_normalizedWeight (v t) (hv t) hn ht
      have he : total (init v n (fun _ : Fin k => (1 : ℝ))) t = n := hval
      have hzero : deficit (init v n (fun _ : Fin k => (1 : ℝ))) n t = 0 := by
        unfold deficit
        rw [he]
        simp [init]
      rw [hzero, Real.rpow_zero]
      exact le_rfl
    · simp [init, nsmul_eq_mul]
  · intro r x hx hi B hsub hB
    have hnew := (small_valid hx hd hsub hB).2
    refine ⟨hi.1, fun t ht => ?_, hi.2.2⟩
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ h) (hnew t)).trans
      (hi.2.1 t ht)
  · intro r x hr hx hi t ht
    let N : ℝ := ((r + 1 : ℕ) : ℝ) + x.samples
    have hN : 0 ≤ N := by dsimp [N]; push_cast; positivity
    have hpaid : N / 3 ≤ total x t := by
      by_cases hz : x.samples = 0
      · rw [hx.exactBefore hz t ht]
        simp only [N, hz, Nat.cast_zero, add_zero, Nat.cast_succ]
        linarith [Nat.cast_nonneg (α := ℝ) r]
      · have hs := hreserve (r + 1) x hx hi t ht (by omega)
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
        unfold deficit at hs
        dsimp [N]
        push_cast at hs ⊢
        linarith
    have he : 2 * β * ((h * (r + 1 + x.samples) : ℕ) : ℝ) = N / 3 := by
      dsimp [β, N]
      push_cast
      field_simp [hh0.ne']
      ring
    exact he ▸ hpaid
  · intro x hx hi t ht
    by_cases hz : x.samples = 0
    · simpa [hx.exactBefore hz t ht] using hβle
    · have hs := hreserve 1 x hx hi t ht (by omega)
      have hsR : (1 : ℝ) ≤ x.samples := by exact_mod_cast (show 1 ≤ x.samples by omega)
      unfold deficit at hs
      norm_num at hs
      linarith

end OnlineMMS.FixedWidth
