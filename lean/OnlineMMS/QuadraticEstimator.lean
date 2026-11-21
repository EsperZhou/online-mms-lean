import OnlineMMS.FixedWidthKernel
import OnlineMMS.BucketBitComplexity
import OnlineMMS.Asymptotic

namespace OnlineMMS.FixedWidth

noncomputable def quadraticMultiplier (k : ℕ) : ℕ :=
  Nat.ceil (4 * Real.sqrt (k : ℝ))

private theorem quadraticMultiplier_bounds {k : ℕ} (hk : 0 < k) :
    1 ≤ quadraticMultiplier k ∧ (k : ℝ) ≤ (quadraticMultiplier k : ℝ)^2 / 16 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hs : 1 ≤ Real.sqrt (k : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have he : (4 : ℝ) * Real.sqrt (k : ℝ) ≤ (quadraticMultiplier k : ℝ) := Nat.le_ceil _
  have hp := pow_le_pow_left₀ (show 0 ≤ 4 * Real.sqrt (k : ℝ) by positivity) he 2
  have he1 : (1 : ℝ) ≤ quadraticMultiplier k := by linarith
  exact ⟨by exact_mod_cast he1, by nlinarith only [hsq, hp]⟩

abbrev History (k : ℕ) := Fin k → List ℝ

private def linearTotal {k : ℕ} (record : History k) : ℝ := ∑ t, (record t).sum

private def pairTotal {k : ℕ} (record : History k) : ℝ := ∑ t, 2 * pairSum (record t)

def QuadInv {m k : ℕ} (h : ℝ) (d : Fin k → ℝ) (r : ℕ)
    (x : State m k (History k)) : Prop :=
  (∀ t z, z ∈ x.stats t → 0 ≤ z ∧ z ≤ 1) ∧
  (∀ t, 0 < d t → deficit x r t ≤ (x.stats t).sum) ∧
  linearTotal x.stats ≤ 2 * (k : ℝ) * x.samples / h ∧
  pairTotal x.stats ≤ (4 * (x.samples : ℝ)^2 - 2 * x.samples) * k / h^2

private theorem pair_diagonal (xs : List ℝ) (hx : ∀ z ∈ xs, 0 ≤ z ∧ z ≤ 1) :
    xs.sum ^ 2 ≤ 2 * pairSum xs + xs.sum := by
  induction xs with
  | nil => norm_num [pairSum]
  | cons x xs ih =>
    have hx' := hx x (by simp)
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    simp only [List.sum_cons, pairSum]
    nlinarith [mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2)]

private theorem quad_reserve {m k r : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : State m k (History k)}
    (hh : 0 < h) (hcap : (k : ℝ) ≤ h^2 / 16) (hr : 0 < r)
    (hv : Valid v d r x) (hi : QuadInv h d r x) (i : Fin k) (ht : 0 < d i) :
    ((r : ℝ) + x.samples) / 4 ≤ total x i := by
  by_cases hz : x.samples = 0
  · rw [hz, hv.exactBefore hz i ht]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  · have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hsR : (1 : ℝ) ≤ x.samples := by exact_mod_cast (show 1 ≤ x.samples by omega)
    let s : ℝ := x.samples
    have hpair : pairTotal x.stats ≤ s^2 / 4 := by
      have h1 := hi.2.2.2
      change pairTotal x.stats ≤ (4 * s^2 - 2 * s) * k / h^2 at h1
      have h2 : (4 * s^2 - 2 * s) * k / h^2 ≤ 4 * s^2 * k / h^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        dsimp [s]
        linarith
      have h3 : 4 * s^2 * k / h^2 ≤ s^2 / 4 := by
        apply (div_le_iff₀ (show 0 < h^2 by positivity)).mpr
        have hm := mul_le_mul_of_nonneg_left hcap (show 0 ≤ (4 : ℝ) * s^2 by positivity)
        nlinarith only [hm]
      exact h1.trans (h2.trans h3)
    have hQ : 2 * pairSum (x.stats i) ≤ pairTotal x.stats :=
      Finset.single_le_sum (fun t _ => mul_nonneg (by norm_num)
        (pairSum_nonneg _ (fun z hz => (hi.1 t z hz).1))) (Finset.mem_univ i)
    have hdiag := pair_diagonal (x.stats i) (hi.1 i)
    have hL : (x.stats i).sum ≤ 1 + s / 2 := by
      by_contra! hbad
      have hprod := mul_pos (sub_pos.mpr hbad) (show 0 < (x.stats i).sum + (1 + s / 2) - 1 by
        change (1 : ℝ) ≤ s at hsR
        linarith)
      have hq := hQ.trans hpair
      change (1 : ℝ) ≤ s at hsR
      nlinarith only [hprod, hq, hdiag, hsR]
    have hD := (hi.2.1 i ht).trans hL
    unfold deficit at hD
    change (1 : ℝ) ≤ s at hsR
    change ((r : ℝ) + s) / 4 ≤ total x i
    change (r : ℝ) + s - total x i ≤ 1 + s / 2 at hD
    linarith

/-- The combined objective has linear and pair increments, encoded by adding
a single fixed profile to the ordered-pair objective. -/
private theorem augmented_objective {k : ℕ} (L : Fin k → ℝ) (a : ℝ)
    (slots : List (Fin k → ℝ)) :
    sampleObjective 1 1 0 (fun _ : Fin k => 0) ((fun t => L t + a / 2) :: slots) =
      a * (∑ t, (slots.map (fun z => z t)).sum) +
        ∑ t, (2 * L t * (slots.map (fun z => z t)).sum + 2 * pairSum (slots.map (fun z => z t))) := by
  unfold sampleObjective
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp [rowObjective, pairSum, List.map_cons]
  ring

private theorem delta_bounds {k : ℕ} {h : ℝ} (hk : 0 < k) (hh : 0 < h)
    (L : Fin k → ℝ) (hL : ∀ t, 0 ≤ L t)
    (means sample : List (Fin k → ℝ))
    (hm₀ : ∀ t z, z ∈ means.map (fun a => a t) → 0 ≤ z)
    (hm₁ : ∀ t, (means.map (fun a => a t)).sum ≤ 1 / h)
    (hs₀ : ∀ t z, z ∈ sample.map (fun a => a t) → 0 ≤ z)
    (hle : let a := (2 * (∑ t, L t) / h + (k : ℝ) / h^2) / ((k : ℝ) / h)
      sampleObjective 1 1 0 (fun _ : Fin k => 0) ((fun t => L t + a / 2) :: sample) ≤
        sampleObjective 1 1 0 (fun _ : Fin k => 0) ((fun t => L t + a / 2) :: means)) :
    (∑ t, (sample.map (fun z => z t)).sum) ≤ 2 * (k : ℝ) / h ∧
    (∑ t, (2 * L t * (sample.map (fun z => z t)).sum +
      2 * pairSum (sample.map (fun z => z t)))) ≤ 4 * (∑ t, L t) / h + 2 * (k : ℝ) / h^2 := by
  let A := (k : ℝ) / h
  let B := 2 * (∑ t, L t) / h + (k : ℝ) / h^2
  let a := B / A
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hA : 0 < A := div_pos hkR hh
  have hB : 0 < B := add_pos_of_nonneg_of_pos
    (div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => hL t))) hh.le) (by positivity)
  have ha : 0 < a := div_pos hB hA
  have hab : a * A = B := div_mul_cancel₀ _ hA.ne'
  let ΔL (slots : List (Fin k → ℝ)) := ∑ t, (slots.map (fun z => z t)).sum
  let ΔQ (slots : List (Fin k → ℝ)) := ∑ t,
    (2 * L t * (slots.map (fun z => z t)).sum + 2 * pairSum (slots.map (fun z => z t)))
  have hmL : ΔL means ≤ A := by
    calc
      _ ≤ ∑ _t : Fin k, 1 / h := Finset.sum_le_sum (fun t _ => hm₁ t)
      _ = _ := by simp [A, nsmul_eq_mul, div_eq_mul_inv]
  have hmQ : ΔQ means ≤ B := by
    calc
      _ ≤ ∑ t, (2 * L t / h + 1 / h^2) := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        let xs := means.map (fun z => z t)
        have hnonneg : 0 ≤ xs.sum := List.sum_nonneg (hm₀ t)
        have hpair := (twice_pairSum_le_sum_sq xs).trans
          (pow_le_pow_left₀ hnonneg (hm₁ t) 2)
        have ht : 2 * L t * xs.sum ≤ 2 * L t * (1 / h) :=
          mul_le_mul_of_nonneg_left (hm₁ t) (mul_nonneg (by norm_num) (hL t))
        change 2 * L t * xs.sum + 2 * pairSum xs ≤ _
        rw [show (1 / h : ℝ)^2 = 1 / h^2 by ring] at hpair
        have he : 2 * L t * (1 / h) = 2 * L t / h := by ring
        rw [he] at ht
        exact add_le_add ht hpair
      _ = B := by
        unfold B
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
        simp [nsmul_eq_mul, div_eq_mul_inv]
  have hsL : 0 ≤ ΔL sample := Finset.sum_nonneg (fun t _ => List.sum_nonneg (hs₀ t))
  have hsQ : 0 ≤ ΔQ sample := Finset.sum_nonneg (fun t _ =>
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hL t)) (List.sum_nonneg (hs₀ t)))
      (mul_nonneg (by norm_num) (pairSum_nonneg _ (hs₀ t))))
  change sampleObjective 1 1 0 _ ((fun t => L t + a / 2) :: sample) ≤
    sampleObjective 1 1 0 _ ((fun t => L t + a / 2) :: means) at hle
  rw [augmented_objective, augmented_objective] at hle
  change a * ΔL sample + ΔQ sample ≤ a * ΔL means + ΔQ means at hle
  have hcost : a * ΔL sample + ΔQ sample ≤ 2 * B := by
    have hm := mul_le_mul_of_nonneg_left hmL ha.le
    linarith
  constructor
  · change ΔL sample ≤ _
    have he : 2 * (k : ℝ) / h = 2 * A := by dsimp [A]; ring
    rw [he]
    apply (mul_le_mul_left ha).mp
    rw [show a * (2 * A) = 2 * B by rw [← hab]; ring]
    linarith
  · change ΔQ sample ≤ _
    have he : 4 * (∑ t, L t) / h + 2 * (k : ℝ) / h^2 = 2 * B := by dsimp [B]; ring
    rw [he]
    linarith [mul_nonneg ha.le hsL]

noncomputable def quadraticPrefix {k : ℕ} (h : ℝ) (record : History k) (i : Fin k) : ℝ :=
  (record i).sum + ((2 * (∑ j, (record j).sum) / h + (k : ℝ) / h^2) /
    ((k : ℝ) / h)) / 2

theorem quadratic_sample_preserves {m k n r h : ℕ} (hk : 0 < k) (hh : 0 < h)
    {v : Fin k → Fin m → ℝ} {x : State m k (History k)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets)
    (gs : List (Fin m)) (hg : List.Forall₂ (fun C g => g ∈ C) buckets gs)
    (hobj : sampleObjective 1 1 0 (fun _ : Fin k => 0)
        ([quadraticPrefix (h : ℝ) x.stats] ++ gs.map (fun g i => x.weight i g)) ≤
      sampleObjective 1 1 0 (fun _ : Fin k => 0)
        ([quadraticPrefix (h : ℝ) x.stats] ++ slotMeans x.weight buckets)) :
    QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) r
      (afterSample x gs (fun i => x.stats i ++ gs.map (x.weight i))) := by
  classical
  let H := h * (r + 1 + x.samples)
  let N : ℝ := ((r + 1 : ℕ) : ℝ) + x.samples
  have hH : 0 < H := Nat.mul_pos hh (by omega)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hN : 0 < N := by dsimp [N]; push_cast; positivity
  let row (i : Fin k) := (x.stats i).sum
  have hrow (i : Fin k) : 0 ≤ row i := List.sum_nonneg (fun z hz => (hi.1 i z hz).1)
  let a := (2 * (∑ i, row i) / h + (k : ℝ) / (h : ℝ)^2) / ((k : ℝ) / h)
  obtain ⟨hsub, hnd⟩ := hb.selected_valid hg
  let means := slotMeans x.weight buckets
  let vals := gs.map (fun g i => x.weight i g)
  have hX (i : Fin k) : (means.map (fun w => w i)).sum ≤ 1 / (h : ℝ) := by
    have hs := slotMeans_sum_le_of_width x.weight buckets x.remaining H hb.pairwise_disjoint
      hb.bucket_size hb.bucket_subsets i (fun g => (hx.weights i g).1)
    refine hs.trans <| (div_le_div_of_nonneg_right (hx.cap i) hH'.le).trans ?_
    have he : (H : ℝ) = (h : ℝ) * N := by dsimp [H, N]; push_cast; rfl
    change N / (H : ℝ) ≤ _
    rw [he]
    have heq : N / ((h : ℝ) * N) = 1 / (h : ℝ) := by field_simp [hN.ne', hhR.ne']; ring
    exact heq.le
  have hvals (i : Fin k) (z : ℝ) (hz : z ∈ gs.map (x.weight i)) : 0 ≤ z ∧ z ≤ 1 := by
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hz
    exact hx.weights i g
  have hmv (i : Fin k) (z : ℝ) (hz : z ∈ means.map (fun a => a i)) : 0 ≤ z :=
    slotMeans_nonneg x.weight buckets i (fun g => (hx.weights i g).1) z hz
  have hsv (i : Fin k) (z : ℝ) (hz : z ∈ vals.map (fun a => a i)) : 0 ≤ z := by
    have hz' : z ∈ gs.map (x.weight i) := by simpa [vals, List.map_map, Function.comp_def] using hz
    exact (hvals i z hz').1
  obtain ⟨hΔL, hΔQ⟩ := delta_bounds hk hhR row hrow means vals hmv hX hsv hobj
  let data := fun i => x.stats i ++ gs.map (x.weight i)
  have hd := (sample_valid hx hsub hnd data).2
  have hsumL : linearTotal data = linearTotal x.stats + ∑ i, (gs.map (x.weight i)).sum := by
    simp only [linearTotal, data, List.sum_append, Finset.sum_add_distrib]
  have hsumQ : pairTotal data = pairTotal x.stats + ∑ i,
      (2 * row i * (gs.map (x.weight i)).sum + 2 * pairSum (gs.map (x.weight i))) := by
    unfold pairTotal
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [data, pairSum_append, row]
    ring
  have hΔL' : (∑ i, (gs.map (x.weight i)).sum) ≤ 2 * (k : ℝ) / h := by
    simpa [vals, List.map_map, Function.comp_def] using hΔL
  have hΔQ' : (∑ i, (2 * row i * (gs.map (x.weight i)).sum +
      2 * pairSum (gs.map (x.weight i)))) ≤ 4 * linearTotal x.stats / h + 2 * (k : ℝ) / (h : ℝ)^2 := by
    simpa [linearTotal, row, vals, List.map_map, Function.comp_def] using hΔQ
  change QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) r (afterSample x gs data)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i z hz
    change z ∈ x.stats i ++ gs.map (x.weight i) at hz
    rcases List.mem_append.mp hz with hp | hp
    · exact hi.1 i z hp
    · exact hvals i z hp
  · intro i ht
    rw [hd i]
    change deficit x (r + 1) i + (gs.map (x.weight i)).sum ≤
      (x.stats i ++ gs.map (x.weight i)).sum
    rw [List.sum_append]
    exact add_le_add_right (hi.2.1 i ht) _
  · change linearTotal data ≤ 2 * (k : ℝ) * ((x.samples + 1 : ℕ) : ℝ) / h
    rw [hsumL]
    calc
      _ ≤ 2 * (k : ℝ) * x.samples / h + 2 * (k : ℝ) / h := add_le_add hi.2.2.1 hΔL'
      _ = _ := by push_cast; ring
  · change pairTotal data ≤ (4 * (((x.samples + 1 : ℕ) : ℝ))^2 -
      2 * ((x.samples + 1 : ℕ) : ℝ)) * k / (h : ℝ)^2
    rw [hsumQ]
    have hrate : 4 * linearTotal x.stats / (h : ℝ) ≤ 8 * (k : ℝ) * x.samples / (h : ℝ)^2 := by
      calc
        _ ≤ 4 * (2 * (k : ℝ) * x.samples / h) / h :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi.2.2.1 (by norm_num)) hhR.le
        _ = _ := by ring
    calc
      _ ≤ (4 * (x.samples : ℝ)^2 - 2 * x.samples) * k / (h : ℝ)^2 +
          (8 * (k : ℝ) * x.samples / (h : ℝ)^2 + 2 * (k : ℝ) / (h : ℝ)^2) :=
        add_le_add hi.2.2.2 (hΔQ'.trans (add_le_add_right hrate _))
      _ = _ := by push_cast; ring

private theorem quadratic_choose {m k n r h : ℕ} (hk : 0 < k) (hh : 0 < h)
    {v : Fin k → Fin m → ℝ} {x : State m k (History k)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets) :
    ∃ gs data, List.Forall₂ (fun C g => g ∈ C) buckets gs ∧
      QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) r (afterSample x gs data) := by
  have hH : 0 < h * (r + 1 + x.samples) := Nat.mul_pos hh (by omega)
  have hnonempty (C : Finset (Fin m)) (hC : C ∈ buckets) : C.Nonempty :=
    Finset.card_pos.mp (hb.bucket_size C hC ▸ hH)
  obtain ⟨gs, hg, hobj⟩ := exists_prefixed_sample_le_mean x.weight 1 1 0 (fun _ => 0)
    [quadraticPrefix (h : ℝ) x.stats] buckets hnonempty
  exact ⟨gs, _, hg, quadratic_sample_preserves hk hh hx hi t buckets hb gs hg hobj⟩

/-- The rational prefixed selector preserves the quadratic estimator's invariant
across rounds. Its input needs only the recorded total for each type. -/
theorem quadratic_rational_sample_preserves {m k n r h : ℕ} (hk : 0 < k) (hh : 0 < h)
    {v : Fin k → Fin m → ℝ} {x : State m k (History k)}
    (hx : Valid v (fun t => truncatedShare (v t) n) (r + 1) x)
    (hi : QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) (r + 1) x)
    (w : Fin k → Fin m → ℚ) (L : Fin k → ℚ)
    (hw : ∀ i g, (w i g : ℝ) = x.weight i g) (hL : ∀ i, (L i : ℝ) = (x.stats i).sum)
    (t : Fin k) (buckets : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h * (r + 1 + x.samples)) x.remaining buckets) :
    let gs := BucketBitComplexity.selectQ w 1 1 0 (fun _ => 0)
      [BucketBitComplexity.quadraticPrefixQ h L] buckets
    List.Forall₂ (fun C g => g ∈ C) buckets gs ∧
      QuadInv (h : ℝ) (fun t => truncatedShare (v t) n) r
        (afterSample x gs (fun i => x.stats i ++ gs.map (x.weight i))) := by
  have hH : 0 < h * (r + 1 + x.samples) := Nat.mul_pos hh (by omega)
  have hnonempty (C : Finset (Fin m)) (hC : C ∈ buckets) : C.Nonempty :=
    Finset.card_pos.mp (hb.bucket_size C hC ▸ hH)
  let pre := BucketBitComplexity.quadraticPrefixQ h L
  let gs := BucketBitComplexity.selectQ w 1 1 0 (fun _ => 0) [pre] buckets
  obtain ⟨hg, hq⟩ := BucketBitComplexity.selectQ_prefixed_objective_le w 1 1 0
    (fun _ => 0) [pre] buckets hnonempty
  change List.Forall₂ (fun C g => g ∈ C) buckets gs ∧ _
  refine ⟨hg, quadratic_sample_preserves hk hh hx hi t buckets hb gs hg ?_⟩
  have hr : (BucketBitComplexity.objectiveQ 1 1 0 (fun _ => 0)
      ([pre] ++ gs.map (fun g i => w i g)) : ℝ) ≤
      (BucketBitComplexity.objectiveQ 1 1 0 (fun _ => 0)
        ([pre] ++ BucketBitComplexity.slotMeansQ w buckets) : ℝ) := by exact_mod_cast hq
  rw [BucketBitComplexity.objectiveQ_cast, BucketBitComplexity.objectiveQ_cast] at hr
  have hwf : (fun i g => (w i g : ℝ)) = x.weight := by funext i g; exact hw i g
  have hpre : (fun i => (pre i : ℝ)) = quadraticPrefix (h : ℝ) x.stats := by
    funext i
    rw [BucketBitComplexity.quadraticPrefixQ_cast]
    simp [quadraticPrefix, hL]
  have hmeans : (BucketBitComplexity.slotMeansQ w buckets).map (fun z i => (z i : ℝ)) =
      slotMeans (fun i g => (w i g : ℝ)) buckets := BucketBitComplexity.slotMeansQ_cast w buckets
  simpa [BucketBitComplexity.realProfiles, List.map_map, Function.comp_def, hpre,
    hmeans, hw, hwf] using hr

def quadraticUpdateQ {m k : ℕ} (L : Fin k → ℚ) (w : Fin k → Fin m → ℚ)
    (gs : List (Fin m)) (i : Fin k) : ℚ := L i + (gs.map (w i)).sum

/-- The rational update maintains the sum of each type's history after a sample. -/
theorem quadraticUpdateQ_cast {m k : ℕ} (L : Fin k → ℚ)
    (w : Fin k → Fin m → ℚ) (gs : List (Fin m)) (record : History k)
    (realW : Fin k → Fin m → ℝ)
    (hL : ∀ i, (L i : ℝ) = (record i).sum) (hw : ∀ i g, (w i g : ℝ) = realW i g)
    (i : Fin k) :
    (quadraticUpdateQ L w gs i : ℝ) = (record i ++ gs.map (realW i)).sum := by
  simp [quadraticUpdateQ, List.sum_append, List.map_map, Function.comp_def, hL, hw]

/-- Supplementary result for the fixed-width policy using the quadratic estimator. -/
theorem quadratic_estimator_guarantee {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n, policy.Guarantees v
      (fun t => truncatedShare (v t) n / (8 * (quadraticMultiplier k : ℝ))) Finset.univ := by
  let h := quadraticMultiplier k
  let β : ℝ := 1 / (8 * (h : ℝ))
  let d : Fin k → ℝ := fun t => truncatedShare (v t) n
  obtain ⟨hh, hcap⟩ := quadraticMultiplier_bounds hk
  change 1 ≤ h at hh
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hd (t : Fin k) : 0 ≤ d t := (truncatedShare_spec (v t) (hv t) hn).1.1
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβle : β ≤ 1 / 4 := by
    dsimp [β]
    apply (div_le_iff₀ (show 0 < (8 : ℝ) * h by positivity)).mpr
    linarith
  suffices hp : ∃ policy : Policy m k n, policy.Guarantees v (fun t => d t * β) Finset.univ by
    simpa [β, h, d, div_eq_mul_inv] using hp
  refine policy_from_estimator hn v hv h (by omega) β hβ (fun _ : Fin k => ([] : List ℝ))
    (QuadInv (h : ℝ) d) ?_ ?_ (fun r x hx hi => quadratic_choose hk (by omega) hx hi) ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [init]
    · intro t ht
      have he : total (init v n (fun _ : Fin k => ([] : List ℝ))) t = n :=
        sum_normalizedWeight (v t) (hv t) hn ht
      unfold deficit
      rw [he]
      simp [init]
    · simp [init, linearTotal]
    · simp [init, pairTotal, pairSum]
  · intro r x hx hi B hsub hB
    have hnew := (small_valid hx hd hsub hB).2
    exact ⟨hi.1, fun t ht => (hnew t).trans (hi.2.1 t ht), hi.2.2⟩
  · intro r x _ hx hi t ht
    have hW := quad_reserve hh0 hcap (by omega : 0 < r + 1) hx hi t ht
    have he : 2 * β * ((h * (r + 1 + x.samples) : ℕ) : ℝ) =
        (((r + 1 : ℕ) : ℝ) + x.samples) / 4 := by
      dsimp [β]; push_cast; field_simp [hh0.ne']; ring
    rw [he]
    exact hW
  · intro x hx hi t ht
    have hW := quad_reserve hh0 hcap (by decide : 0 < 1) hx hi t ht
    norm_num at hW
    have hs : (0 : ℝ) ≤ x.samples := Nat.cast_nonneg _
    linarith

end OnlineMMS.FixedWidth
