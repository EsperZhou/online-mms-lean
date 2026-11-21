import OnlineMMS.Benchmarks
import OnlineMMS.Buckets
import OnlineMMS.Reserve
import OnlineMMS.Sampling
import OnlineMMS.Trimming
import OnlineMMS.PolicyTrace

namespace OnlineMMS

structure AlgorithmState (m k : ℕ) where
  remaining : Finset (Fin m)
  sampleCount : ℕ
  weight : Fin k → Fin m → ℝ
  products : Fin k → ℝ

namespace AlgorithmState

private def total {m k : ℕ} (x : AlgorithmState m k) (t : Fin k) : ℝ :=
  bundleValue (x.weight t) x.remaining

private def deficit {m k : ℕ} (x : AlgorithmState m k) (r : ℕ) (t : Fin k) : ℝ :=
  (r : ℝ) + x.sampleCount - x.total t

private structure Valid {m k : ℕ} (h : ℝ) (v : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (x : AlgorithmState m k) : Prop where
  weightBounds : ∀ t g, 0 ≤ x.weight t g ∧ x.weight t g ≤ 1
  valueBounds : ∀ t g, d t * x.weight t g ≤ v t g
  totalBound : ∀ t, x.total t ≤ (r : ℝ) + x.sampleCount
  exactBeforeSample : x.sampleCount = 0 → ∀ t, 0 < d t → x.total t = r
  firstDeficit : x.sampleCount = 1 → ∀ t, 0 < d t → x.deficit r t ≤ 2 - threshold h
  productNonneg : ∀ t, 0 ≤ x.products t
  productLower : 0 < x.sampleCount → ∀ t, 0 < d t → h ^ x.deficit r t ≤ x.products t
  productUpper : 0 < x.sampleCount →
    ∑ t, x.products t ≤ h ^ (3 : ℕ) / 64 * Real.exp (4 * ((x.sampleCount : ℝ) - 1))
  zeroWeight : ∀ t, d t = 0 → ∀ g, x.weight t g = 0

private theorem sum_remove {m : ℕ} (w : Fin m → ℝ)
    {remaining bundle : Finset (Fin m)} (hsub : bundle ⊆ remaining) :
    bundleValue w (remaining \ bundle) = bundleValue w remaining - bundleValue w bundle := by
  unfold bundleValue
  have h := Finset.sum_sdiff hsub (f := w)
  linarith

private theorem laterDeficit {m k r : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : AlgorithmState m k} (hx : Valid h v d r x)
    (hh : 216 ≤ h) (hs : 2 ≤ x.sampleCount) (t : Fin k) (ht : 0 < d t) :
    x.deficit r t ≤ 3 - threshold h + (3 / 4 : ℝ) * ((x.sampleCount : ℝ) - 2) := by
  have hs' : 0 < x.sampleCount := by omega
  have hprod := (hx.productLower hs' t ht).trans <|
    (Finset.single_le_sum (fun i _ => hx.productNonneg i) (Finset.mem_univ t)).trans
      (hx.productUpper hs')
  apply later_deficit_budget hh (by exact_mod_cast hs)
  rw [mul_comm (x.deficit r t) (Real.log h), ← Real.rpow_def_of_pos (by linarith : 0 < h)]
  exact hprod

private theorem valued {m k : ℕ} {v : Fin k → Fin m → ℝ} {d : Fin k → ℝ}
    {x : AlgorithmState m k} {t : Fin k} {bundle : Finset (Fin m)} {β : ℝ}
    (hd : 0 ≤ d t) (hdom : ∀ g, d t * x.weight t g ≤ v t g)
    (hpay : β ≤ bundleValue (x.weight t) bundle) :
    d t * β ≤ bundleValue (v t) bundle := by
  calc
    _ ≤ d t * bundleValue (x.weight t) bundle := mul_le_mul_of_nonneg_left hpay hd
    _ = ∑ g ∈ bundle, d t * x.weight t g := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun g _ => hdom g)

private theorem weight_list_sum {m : ℕ} (w : Fin m → ℝ) (gs : List (Fin m))
    (hnd : gs.Nodup) : (gs.map w).sum = bundleValue w gs.toFinset := by
  induction gs with
  | nil => simp [bundleValue]
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := List.nodup_cons.mp hnd
    have hnot : g ∉ gs.toFinset := by simpa using hg
    simp [bundleValue, Finset.sum_insert hnot, ih hgs]

private noncomputable def smallNext {m k : ℕ} (r : ℕ) (x : AlgorithmState m k)
    (bundle : Finset (Fin m)) : AlgorithmState m k :=
  let remaining := x.remaining \ bundle
  ⟨remaining, x.sampleCount, fun t =>
    trimWeights remaining (x.weight t) ((r : ℝ) + x.sampleCount), x.products⟩

private theorem after_small {m k r : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : AlgorithmState m k} (hx : Valid h v d (r + 1) x)
    (hh : 1 ≤ h) (hd : ∀ t, 0 ≤ d t) {bundle : Finset (Fin m)} (hsub : bundle ⊆ x.remaining)
    (hsmall : ∀ t, bundleValue (x.weight t) bundle ≤ 1) :
    Valid h v d r (smallNext r x bundle) := by
  let nextR := x.remaining \ bundle
  let cap := (r : ℝ) + x.sampleCount
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  have trim (t : Fin k) := trimWeights_spec nextR (x.weight t)
    (fun g => (hx.weightBounds t g).1) cap hcap
  let next := smallNext r x bundle
  have hw (t : Fin k) (g : Fin m) := (trim t).1 g
  have htotal (t : Fin k) := (trim t).2
  change Valid h v d r next
  have total_next (t : Fin k) :
      next.total t = min (x.total t - bundleValue (x.weight t) bundle) cap := by
    exact (htotal t).trans (congrArg (fun z => min z cap) (sum_remove _ hsub))
  have hreserve (t : Fin k) :
      next.total t ≤ cap ∧ next.deficit r t ≤ x.deficit (r + 1) t := by
    rw [AlgorithmState.deficit, AlgorithmState.deficit, total_next]
    change min (x.total t - bundleValue (x.weight t) bundle) cap ≤ cap ∧
      cap - min (x.total t - bundleValue (x.weight t) bundle) cap ≤
        ((r + 1 : ℕ) : ℝ) + x.sampleCount - x.total t
    have haW : bundleValue (x.weight t) bundle ≤ x.total t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => (hx.weightBounds t g).1)
    have hN : ((r + 1 : ℕ) : ℝ) + x.sampleCount = cap + 1 := by
      dsimp [cap]
      push_cast
      ring
    have h := trim_reserve (N := cap + 1) (by linarith) (hN ▸ hx.totalBound t) haW (hsmall t)
    rw [hN]
    simpa only [add_sub_cancel_right] using h.2
  refine ⟨fun t g => ⟨(hw t g).1, (hw t g).2.trans (hx.weightBounds t g).2⟩,
    ?_, fun t => (hreserve t).1, ?_, ?_, hx.productNonneg, ?_, hx.productUpper, ?_⟩
  · intro t g
    exact (mul_le_mul_of_nonneg_left (hw t g).2 (hd t)).trans (hx.valueBounds t g)
  · intro hs t ht
    change x.sampleCount = 0 at hs
    obtain ⟨hu, hl⟩ := hreserve t
    have he := hx.exactBeforeSample hs t ht
    change next.total t ≤ (r : ℝ) + x.sampleCount at hu
    change (r : ℝ) + x.sampleCount - next.total t ≤
      ((r + 1 : ℕ) : ℝ) + x.sampleCount - x.total t at hl
    rw [he] at hl
    simp [hs] at hu hl
    exact le_antisymm hu hl
  · intro hs t ht
    exact (hreserve t).2.trans (hx.firstDeficit hs t ht)
  · intro hs t ht
    exact (Real.rpow_le_rpow_of_exponent_le hh (hreserve t).2).trans
      (hx.productLower hs t ht)
  · intro t ht g
    exact le_antisymm ((hw t g).2.trans_eq (hx.zeroWeight t ht g)) (hw t g).1

private def sampleProducts {m k : ℕ} (h : ℝ) (x : AlgorithmState m k)
    (gs : List (Fin m)) (t : Fin k) : ℝ :=
  x.products t * sampleProduct h (gs.map (x.weight t))

private def sampleNext {m k : ℕ} (h : ℝ) (x : AlgorithmState m k)
    (gs : List (Fin m)) : AlgorithmState m k :=
  ⟨x.remaining \ gs.toFinset, x.sampleCount + 1, x.weight, sampleProducts h x gs⟩

private theorem after_sample {m k r : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : AlgorithmState m k} (hx : Valid h v d (r + 1) x)
    (hh : 1 ≤ h) (gs : List (Fin m))
    (hsub : gs.toFinset ⊆ x.remaining) (hnd : gs.Nodup)
    (hone : x.sampleCount = 0 → ∀ t, x.products t = 1)
    (hfb : x.sampleCount = 0 → ∀ t,
      (gs.map (x.weight t)).sum ≤ 2 - threshold h)
    (hp : (∑ t, sampleProducts h x gs t) ≤
      h ^ (3 : ℕ) / 64 * Real.exp (4 * (x.sampleCount : ℝ))) :
    Valid h v d r (sampleNext h x gs) := by
  let next := sampleNext h x gs
  change Valid h v d r next
  have hnonneg (t : Fin k) : ∀ z ∈ gs.map (x.weight t), 0 ≤ z ∧ z ≤ 1 := by
    intro z hz
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hz
    exact hx.weightBounds t g
  have heq (t : Fin k) :
      next.deficit r t = x.deficit (r + 1) t + (gs.map (x.weight t)).sum := by
    rw [AlgorithmState.deficit, AlgorithmState.deficit, weight_list_sum _ _ hnd]
    change (r : ℝ) + ((x.sampleCount + 1 : ℕ) : ℝ) -
        bundleValue (x.weight t) (x.remaining \ gs.toFinset) = _
    rw [sum_remove _ hsub]
    unfold AlgorithmState.total
    push_cast
    convert sample_deficit ((r : ℝ) + x.sampleCount + 1)
      (bundleValue (x.weight t) x.remaining) (bundleValue (x.weight t) gs.toFinset) using 1
      <;> ring
  have hzero (hs : x.sampleCount = 0) (t : Fin k) (ht : 0 < d t) :
      x.deficit (r + 1) t = 0 := by
    simp [AlgorithmState.deficit, hs, hx.exactBeforeSample hs t ht]
  have hstep (t : Fin k) (ht : 0 < d t) :
      h ^ x.deficit (r + 1) t ≤ x.products t := by
    by_cases hs : x.sampleCount = 0
    · simp [hzero hs t ht, hone hs t]
    · exact hx.productLower (by omega) t ht
  refine ⟨hx.weightBounds, hx.valueBounds, ?_, ?_, ?_, ?_, ?_, ?_, hx.zeroWeight⟩
  · intro t
    have hW := hx.totalBound t
    have hsum : 0 ≤ (gs.map (x.weight t)).sum := by
      exact List.sum_nonneg (fun z hz => (hnonneg t z hz).1)
    have hD := heq t
    simp only [AlgorithmState.deficit, next, sampleNext, Nat.cast_add, Nat.cast_one] at hD hW ⊢
    linarith
  · change x.sampleCount + 1 = 0 → _
    omega
  · intro hs t ht
    have hz : x.sampleCount = 0 := by change x.sampleCount + 1 = 1 at hs; omega
    rw [heq, hzero hz t ht, zero_add]
    exact hfb hz t
  · intro t
    exact mul_nonneg (hx.productNonneg t)
      (sampleProduct_nonneg hh _ (fun z hz => (hnonneg t z hz).1))
  · intro _ t ht
    rw [heq]
    exact rpow_deficit_add_le hh _ (hnonneg t) (hstep t ht)
  · intro _
    have he : ((next.sampleCount : ℝ) - 1) = (x.sampleCount : ℝ) := by
      simp [next, sampleNext, Nat.cast_add]
    simpa only [he] using hp

/-- Products stay exactly one along histories that have taken no sample. -/
private def Invariant {m k : ℕ} (h : ℝ) (v : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (x : AlgorithmState m k) : Prop :=
  r = 0 ∨ (Valid h v d r x ∧ (x.sampleCount = 0 → ∀ t, x.products t = 1))

private theorem sample_correct {m k r H : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {x : AlgorithmState m k} (hx : Valid h v d (r + 1) x)
    (hone : x.sampleCount = 0 → ∀ t, x.products t = 1)
    (hh : 216 ≤ h) (hk : (k : ℝ) ≤ 2 * (h - 212) ^ 2)
    (hwidth : 0 < H) (t : Fin k) (ht : 0 < d t)
    (hsmall : ∀ g ∈ x.remaining, x.weight t g ≤ threshold h)
    (hfirstWidth : x.sampleCount = 0 → (H : ℝ) = h * ((r + 1 : ℕ) + (x.sampleCount : ℝ)))
    (hlaterWidth : x.sampleCount ≠ 0 → (H : ℝ) = h / 4 * ((r + 1 : ℕ) + (x.sampleCount : ℝ)))
    (hR : 2 ≤ r + 1) {buckets : List (Finset (Fin m))} {gs : List (Fin m)}
    (hb : SortedBuckets (x.weight t) H x.remaining buckets)
    (hgreedy : IsGreedySample x.weight h
      (if x.sampleCount = 0 then 1 else 0)
      (if x.sampleCount = 0 then 128 / h ^ 3 else 1)
      x.products [] buckets gs) :
    gs.toFinset ⊆ x.remaining ∧
      d t * threshold h ≤ bundleValue (v t) gs.toFinset ∧
      Invariant h v d r (sampleNext h x gs) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ) + x.sampleCount
  have hN : 0 < N := by
    dsimp [N]
    push_cast
    positivity
  have hh' : 1 ≤ h := by linarith
  have hβ : 0 ≤ threshold h := by unfold threshold; positivity
  have hH : 0 < (H : ℝ) := by exact_mod_cast hwidth
  have hmeans (i : Fin k) : ∀ z ∈ (slotMeans x.weight buckets).map (fun z => z i), 0 ≤ z :=
    slotMeans_nonneg _ _ _ (fun g => (hx.weightBounds i g).1)
  have hmean (i : Fin k) :
      ((slotMeans x.weight buckets).map (fun z => z i)).sum ≤ N / H :=
    (slotMeans_sum_le_of_width x.weight _ _ _ hb.pairwise_disjoint
      hb.bucket_size hb.bucket_subsets i (fun g => (hx.weightBounds i g).1)).trans <|
        div_le_div_of_nonneg_right (hx.totalBound i) hH.le
  have hselected {gs : List (Fin m)}
      (hg : List.Forall₂ (fun B g => g ∈ B) buckets gs) :=
    hb.selected_valid hg
  have hsorted {gs : List (Fin m)}
      (hg : List.Forall₂ (fun B g => g ∈ B) buckets gs) :
      x.total t / H - threshold h ≤ (gs.map (x.weight t)).sum := by
    have hpay := hb.payment hg (fun g => (hx.weightBounds t g).1) hβ hsmall
    apply sub_le_iff_le_add.mpr
    rw [add_comm]
    apply (div_le_iff₀ hH).mpr
    simpa [mul_comm] using hpay
  have hwidthDiv {a : ℝ} (ha : a ≠ 0) :
      N / (a * N) = 1 / a := by
    field_simp [ha, ne_of_gt hN]
    exact mul_comm _ _
  have hnonfinal : N / 4 ≤ x.total t := by
    have h := nonfinal_reserve hh hR
      (fun hs => by simp [hs, hx.exactBeforeSample hs t ht])
      (fun hs => hx.firstDeficit hs t ht)
      (fun hs => laterDeficit hx hh hs t ht)
    linarith
  by_cases hs : x.sampleCount = 0
  · have hfirst : (H : ℝ) = h * N := hfirstWidth hs
    have hmass (i : Fin k) :
        ((slotMeans x.weight buckets).map (fun z => z i)).sum ≤ 1 / h := by
      simpa only [hfirst, hwidthDiv (by linarith : h ≠ 0)] using hmean i
    have hfirstGreedy : IsGreedySample x.weight h 1 (128 / h ^ 3) (fun _ => 1) [] buckets gs := by
      have he : x.products = fun _ => 1 := funext (hone hs)
      simpa only [hs, if_pos rfl, he] using hgreedy
    obtain ⟨hg, hobj⟩ := greedy_sample_le_mean x.weight h 1 (128 / h ^ 3)
      (fun _ => 1) buckets gs hfirstGreedy
    obtain ⟨hsub, hnd⟩ := hselected hg
    have hmeanBound := firstSample_mean_bound hh' (slotMeans x.weight buckets) hmeans hmass
    have hobjBound : sampleObjective h 1 (128 / h ^ 3) (fun _ => 1)
        (gs.map (fun g i => x.weight i g)) ≤ 2 - 1 / h :=
      hobj.trans ((by simpa using hmeanBound :
        sampleObjective h 1 (128 / h ^ 3) (fun _ => 1) (slotMeans x.weight buckets) ≤
          (k : ℝ) / h ^ 2 * (1 + 384 / h)).trans (first_objective_bound hh hk))
    have hslots : ∀ z ∈ gs.map (fun g i => x.weight i g),
        ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
      intro z hz i
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hz
      exact hx.weightBounds i g
    obtain ⟨hdeficit, hproducts⟩ := firstSample_bounds_of_objective hh' _ hslots hobjBound
    have hpay := hsorted hg
    have htotal : x.total t = N := by simp [N, hs, hx.exactBeforeSample hs t ht]
    rw [htotal, hfirst] at hpay
    have hpaid := first_sample_payment hh hN hpay
    rw [weight_list_sum _ _ hnd] at hpaid
    have hp : (∑ i, sampleProducts h x gs i) ≤
        h ^ (3 : ℕ) / 64 * Real.exp (4 * (x.sampleCount : ℝ)) := by
      simpa [sampleProducts, hs, hone hs, List.map_map, Function.comp_def] using hproducts
    have hvalid := after_sample hx hh' gs hsub hnd hone
      (fun _ i => by simpa [List.map_map, Function.comp_def, threshold] using hdeficit i) hp
    refine ⟨hsub, valued ht.le (hx.valueBounds t) hpaid, Or.inr ⟨hvalid, ?_⟩⟩
    intro hz
    change x.sampleCount + 1 = 0 at hz
    omega
  · have hlast : (H : ℝ) = h / 4 * N := hlaterWidth hs
    have hmass (i : Fin k) :
        ((slotMeans x.weight buckets).map (fun z => z i)).sum ≤ 4 / h := by
      have hh4 : h / 4 ≠ 0 := by positivity
      have he : 1 / (h / 4) = 4 / h := by ring
      simpa only [hlast, hwidthDiv hh4, he] using hmean i
    have hlaterGreedy : IsGreedySample x.weight h 0 1 x.products [] buckets gs := by
      simpa only [if_neg hs] using hgreedy
    obtain ⟨hg, hobj⟩ := greedy_sample_le_mean x.weight h 0 1 x.products buckets gs hlaterGreedy
    obtain ⟨hsub, hnd⟩ := hselected hg
    have hproduct := hobj.trans (laterSample_mean_bound hh' x.products hx.productNonneg
      (slotMeans x.weight buckets) hmeans hmass)
    have hp : (∑ i, sampleProducts h x gs i) ≤
        h ^ (3 : ℕ) / 64 * Real.exp (4 * (x.sampleCount : ℝ)) := by
      apply product_budget_step (hx.productUpper (by omega))
      simpa [sampleProducts, sampleObjective, rowObjective, List.map_map, Function.comp_def] using hproduct
    have hpay := hsorted hg
    rw [hlast] at hpay
    have hpaid := later_sample_payment hh hN hnonfinal hpay
    rw [weight_list_sum _ _ hnd] at hpaid
    have hvalid := after_sample hx hh' gs hsub hnd hone
      (fun hz => False.elim (hs hz)) hp
    refine ⟨hsub, valued ht.le (hx.valueBounds t) hpaid, Or.inr ⟨hvalid, ?_⟩⟩
    intro hz
    change x.sampleCount + 1 = 0 at hz
    omega

private def sampleWidth {m k : ℕ} (h b r : ℕ) (x : AlgorithmState m k) : ℕ :=
  (if x.sampleCount = 0 then h else b) * (r + 1 + x.sampleCount)

private def finalNext {m k : ℕ} (x : AlgorithmState m k) : AlgorithmState m k :=
  ⟨∅, x.sampleCount, x.weight, x.products⟩

private noncomputable def protectedTypes {k : ℕ} (d : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun t => 0 < d t)

private theorem zero_outside_protected {m k : ℕ} {h : ℝ} {v : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {r : ℕ} {x : AlgorithmState m k} (hx : Valid h v d r x)
    (hd : ∀ t, 0 ≤ d t) (t : Fin k) (ht : t ∉ protectedTypes d) (g : Fin m) :
    x.weight t g = 0 := by
  have hnonpos : d t ≤ 0 := le_of_not_gt (by simpa [protectedTypes] using ht)
  exact hx.zeroWeight t (le_antisymm hnonpos (hd t)) g

/-- One execution step of Algorithm 1. Here (r+1) agents remain before
the step. Equal-weight bucket boundaries and tied score minimizers may be
resolved in any order. For singleton payments the first qualifying good
in index order is used. -/
inductive Step {m k : ℕ} (h b : ℕ) (d : Fin k → ℝ) (r : ℕ)
    (x : AlgorithmState m k) (t : Fin k) :
    Finset (Fin m) → AlgorithmState m k → Prop
  | final (hr : r = 0) : Step h b d r x t x.remaining (finalNext x)
  | empty (hr : r ≠ 0) (hz : d t = 0) : Step h b d r x t ∅ (smallNext r x ∅)
  | singleton {g : Fin m} (hr : r ≠ 0) (ht : 0 < d t) (hg : g ∈ x.remaining)
      (hpay : threshold h ≤ x.weight t g)
      (hfirst : ∀ a ∈ x.remaining, threshold h ≤ x.weight t a → g ≤ a) :
      Step h b d r x t {g} (smallNext r x {g})
  | sample {buckets : List (Finset (Fin m))} {gs : List (Fin m)}
      (hr : r ≠ 0) (ht : 0 < d t)
      (hsmall : ∀ g ∈ x.remaining, x.weight t g < threshold h)
      (hsorted : SortedBuckets (x.weight t) (sampleWidth h b r x) x.remaining buckets)
      (hgreedy : IsProtectedGreedySample x.weight (h : ℝ)
        (if x.sampleCount = 0 then 1 else 0)
        (if x.sampleCount = 0 then 128 / (h : ℝ) ^ 3 else 1)
        x.products (protectedTypes d) [] buckets gs) :
      Step h b d r x t gs.toFinset (sampleNext h x gs)

private theorem width_pos {m k h b : ℕ}
    (hb : h = 4 * b) (hh : (216 : ℝ) ≤ h) (r : ℕ) (x : AlgorithmState m k) :
    0 < sampleWidth h b r x := by
  have hh' : 0 < h := by
    have : (0 : ℝ) < h := by linarith
    exact_mod_cast this
  have hb' : 0 < b := by omega
  have hr : 0 < r + 1 + x.sampleCount := by omega
  unfold sampleWidth
  split <;> exact Nat.mul_pos (by assumption) hr

private theorem step_correct {m k : ℕ} {h b : ℕ} (hb : h = 4 * b)
    (hh : (216 : ℝ) ≤ h) (hk : (k : ℝ) ≤ 2 * ((h : ℝ) - 212) ^ 2)
    {v : Fin k → Fin m → ℝ} (hv : ∀ t g, 0 ≤ v t g)
    {d : Fin k → ℝ} (hd : ∀ t, 0 ≤ d t)
    (r : ℕ) (x : AlgorithmState m k) (t : Fin k) (bundle : Finset (Fin m))
    (next : AlgorithmState m k) (valid : Invariant (h : ℝ) v d (r + 1) x)
    (hstep : Step h b d r x t bundle next) :
    bundle ⊆ x.remaining ∧ d t * threshold h ≤ bundleValue (v t) bundle ∧
      next.remaining = x.remaining \ bundle ∧ Invariant (h : ℝ) v d r next := by
  rcases valid with hzero | ⟨hx, hone⟩
  · omega
  have hh' : (1 : ℝ) ≤ h := by linarith
  have small (G : Finset (Fin m)) (hsub : G ⊆ x.remaining)
      (hsize : ∀ i, bundleValue (x.weight i) G ≤ 1)
      (hpay : d t * threshold h ≤ bundleValue (v t) G) :
      G ⊆ x.remaining ∧ d t * threshold h ≤ bundleValue (v t) G ∧
        (smallNext r x G).remaining = x.remaining \ G ∧
        Invariant (h : ℝ) v d r (smallNext r x G) :=
    ⟨hsub, hpay, rfl, Or.inr ⟨after_small hx hh' hd hsub hsize, hone⟩⟩
  cases hstep with
  | final hr =>
    subst r
    refine ⟨Finset.Subset.refl _, ?_, by simp [finalNext], Or.inl rfl⟩
    by_cases ht : 0 < d t
    · apply valued (x := x) ht.le (hx.valueBounds t)
      apply final_reserve hh (s := x.sampleCount)
      · intro hs
        simpa [hs] using hx.exactBeforeSample hs t ht
      · intro hs
        simpa [AlgorithmState.deficit] using hx.firstDeficit hs t ht
      · intro hs
        simpa [AlgorithmState.deficit] using laterDeficit hx hh hs t ht
    · rw [le_antisymm (le_of_not_gt ht) (hd t), zero_mul]
      exact Finset.sum_nonneg (fun g _ => hv t g)
  | empty _ hz =>
    exact small ∅ (Finset.empty_subset _) (fun _ => by simp [bundleValue])
      (by simp [hz, bundleValue])
  | @singleton g _ ht hg hpay _ =>
    exact small {g} (Finset.singleton_subset_iff.mpr hg)
      (fun i => by simpa [bundleValue] using (hx.weightBounds i g).2)
      (valued ht.le (hx.valueBounds t) (by simpa [bundleValue] using hpay))
  | @sample buckets gs hr ht hsmall hsorted hgreedy =>
    have hgreedy' := (greedy_sample_iff_protected x.weight (h : ℝ)
        (if x.sampleCount = 0 then 1 else 0)
        (if x.sampleCount = 0 then 128 / (h : ℝ) ^ 3 else 1)
        x.products (protectedTypes d) (zero_outside_protected hx hd) buckets gs).mpr hgreedy
    obtain ⟨hsub, hpay, hvalid⟩ := sample_correct hx hone hh hk (width_pos hb hh r x)
      t ht (fun g hg => (hsmall g hg).le)
      (fun hs => by simp [sampleWidth, hs, Nat.cast_add, Nat.cast_mul])
      (fun hs => by
        have hbr : (h : ℝ) / 4 = (b : ℝ) := by rw [hb]; push_cast; ring
        simp [sampleWidth, hs, Nat.cast_add, Nat.cast_mul, hbr])
      (by omega) hsorted hgreedy'
    exact ⟨hsub, hpay, rfl, hvalid⟩

private theorem step_exists {m k h b : ℕ} (hb : h = 4 * b)
    (hh : (216 : ℝ) ≤ h) {d : Fin k → ℝ} (hd : ∀ t, 0 ≤ d t)
    (r : ℕ) (x : AlgorithmState m k) (t : Fin k)
    (hzero : ∀ i, i ∉ protectedTypes d → ∀ g, x.weight i g = 0) :
    ∃ bundle next, Step h b d r x t bundle next := by
  classical
  by_cases hr : r = 0
  · exact ⟨_, _, .final hr⟩
  by_cases ht : 0 < d t
  · let eligible := x.remaining.filter (fun g => threshold h ≤ x.weight t g)
    by_cases he : eligible.Nonempty
    · let g := eligible.min' he
      have hg := Finset.mem_filter.mp (eligible.min'_mem he)
      exact ⟨_, _, .singleton hr ht hg.1 hg.2
        (fun a ha hpay => eligible.min'_le a (Finset.mem_filter.mpr ⟨ha, hpay⟩))⟩
    · have hsmall (g : Fin m) (hg : g ∈ x.remaining) : x.weight t g < threshold h :=
        lt_of_not_ge (fun hpay => he ⟨g, Finset.mem_filter.mpr ⟨hg, hpay⟩⟩)
      have hH := width_pos hb hh r x
      obtain ⟨buckets, hsorted⟩ :=
        SortedBuckets.exists_buckets (w := x.weight t) hH x.remaining
      have hne (B : Finset (Fin m)) (hB : B ∈ buckets) : B.Nonempty :=
        Finset.card_pos.mp (hsorted.bucket_size B hB ▸ hH)
      obtain ⟨gs, _, hgreedy, _⟩ := exists_greedy_sample_le_mean
        x.weight (h : ℝ) (if x.sampleCount = 0 then 1 else 0)
        (if x.sampleCount = 0 then 128 / (h : ℝ) ^ 3 else 1) x.products buckets hne
      have hp := (greedy_sample_iff_protected x.weight (h : ℝ)
        (if x.sampleCount = 0 then 1 else 0)
        (if x.sampleCount = 0 then 128 / (h : ℝ) ^ 3 else 1)
        x.products (protectedTypes d) hzero buckets gs).mp hgreedy
      exact ⟨gs.toFinset, _, .sample hr ht hsmall hsorted hp⟩
  · exact ⟨_, _, .empty hr (le_antisymm (le_of_not_gt ht) (hd t))⟩

end AlgorithmState

private noncomputable def algorithmInitial {m k : ℕ} (n : ℕ)
    (v : Fin k → Fin m → ℝ) : AlgorithmState m k :=
  ⟨Finset.univ, 0, fun t => normalizedWeight (v t) n, fun _ => 1⟩

/-- A policy is an execution of the manuscript's Algorithm 1 if every
edge follows its update rule and its child starts in the resulting state. -/
def FollowsAlgorithm1 {m n k : ℕ} (v : Fin k → Fin m → ℝ)
    (policy : Policy m k n) : Prop :=
  policy.Follows (AlgorithmState.Step (bucketMultiplier k) (bucketMultiplier k / 4)
    (fun t => truncatedShare (v t) n)) (algorithmInitial n v)

/-- Algorithm 1 has a legal execution on every instance. Every execution
pays at least the stated fraction of each arrival's original TPS. -/
theorem general_algorithm1_certified {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    (∃ policy : Policy m k n, FollowsAlgorithm1 v policy) ∧
    ∀ policy : Policy m k n, FollowsAlgorithm1 v policy →
      policy.Guarantees v (fun t => truncatedShare (v t) n / (2 * (bucketMultiplier k : ℝ)))
        Finset.univ := by
  classical
  let h := bucketMultiplier k
  let d : Fin k → ℝ := fun t => truncatedShare (v t) n
  have hd (t : Fin k) : 0 ≤ d t := (truncatedShare_spec (v t) (hv t) hn).1.1
  obtain ⟨hh, ⟨b, hb⟩, hk'⟩ := bucketMultiplier_bounds hk
  change 216 ≤ h at hh
  change h = 4 * b at hb
  change k ≤ 2 * (h - 212) ^ 2 at hk'
  have hhR : (216 : ℝ) ≤ h := by exact_mod_cast hh
  have hkCast : (k : ℝ) ≤ ((2 * (h - 212) ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hk'
  have hkR : (k : ℝ) ≤ 2 * ((h : ℝ) - 212) ^ 2 := by
    push_cast [Nat.cast_sub (show 212 ≤ h by omega)] at hkCast
    exact hkCast
  let init := algorithmInitial n v
  have hinit : AlgorithmState.Invariant (h : ℝ) v d n init := by
    have hweights (t : Fin k) : 0 < d t → init.total t = n :=
      sum_normalizedWeight (v t) (hv t) hn
    have hzero (t : Fin k) (ht : ¬0 < d t) :
        ∀ g, normalizedWeight (v t) n g = 0 := by
      intro g
      have he : truncatedShare (v t) n = 0 :=
        le_antisymm (le_of_not_gt ht) (hd t)
      simp [normalizedWeight, he]
    refine Or.inr ⟨⟨?_, ?_, ?_, fun _ => hweights, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => rfl⟩
    · intro t g
      by_cases ht : 0 < d t
      · exact ⟨normalizedWeight_nonneg (v t) (hv t) ht g,
          normalizedWeight_le_one (v t) ht g⟩
      · change 0 ≤ normalizedWeight (v t) n g ∧ normalizedWeight (v t) n g ≤ 1
        rw [hzero t ht g]
        norm_num
    · intro t g
      by_cases ht : 0 < d t
      · exact truncatedShare_mul_normalizedWeight_le (v t) ht g
      · change d t * normalizedWeight (v t) n g ≤ v t g
        simpa [hzero t ht g] using hv t g
    · intro t
      by_cases ht : 0 < d t
      · rw [hweights t ht]
        simp [init, algorithmInitial]
      · simp [AlgorithmState.total, bundleValue, init, algorithmInitial, hzero t ht]
    · simp [init, algorithmInitial]
    · exact fun _ => zero_le_one
    · simp [init, algorithmInitial]
    · simp [init, algorithmInitial]
    · intro t ht g
      exact hzero t (fun hpos => (ne_of_gt hpos) ht) g
  have hbdiv : h / 4 = b := by omega
  have hstep := AlgorithmState.step_correct hb hhR hkR hv hd
  constructor
  · change ∃ p : Policy m k n, p.Follows (AlgorithmState.Step h (h / 4) d) init
    rw [hbdiv]
    apply Policy.follows_of_steps _ (AlgorithmState.Invariant (h : ℝ) v d) _ n init hinit
    intro r state hs t
    have hzero : ∀ i, i ∉ AlgorithmState.protectedTypes d → ∀ g, state.weight i g = 0 := by
      rcases hs with hz | ⟨hx, _⟩
      · omega
      · exact AlgorithmState.zero_outside_protected hx hd
    obtain ⟨bundle, next, hrun⟩ := AlgorithmState.step_exists hb hhR hd r state t hzero
    exact ⟨bundle, next, hrun, (hstep r state t bundle next hs hrun).2.2.2⟩
  · intro policy hp
    change policy.Follows (AlgorithmState.Step h (h / 4) d) init at hp
    rw [hbdiv] at hp
    have hpay := hp.guarantees (AlgorithmState.Invariant (h : ℝ) v d)
      AlgorithmState.remaining v (fun t => d t * threshold h) hstep hinit
    simpa [init, algorithmInitial, d, h, threshold, div_eq_mul_inv] using hpay

/-- The guarantee in Theorem 3.1 for the original TPS. -/
theorem general_tps_guarantee {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => truncatedShare (v t) n / (2 * (bucketMultiplier k : ℝ)))
        Finset.univ := by
  obtain ⟨⟨policy, hp⟩, hcorrect⟩ := general_algorithm1_certified hn hk v hv
  exact ⟨policy, hcorrect policy hp⟩

/-- Every execution of Algorithm 1 also meets the stated original-MMS target. -/
theorem algorithm1_mms_of_follows {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (policy : Policy m k n) (hp : FollowsAlgorithm1 v policy) :
    policy.Guarantees v (fun t => maximinShare (v t) n hn / (2 * (bucketMultiplier k : ℝ)))
      Finset.univ :=
  ((general_algorithm1_certified hn hk v hv).2 policy hp).mono (fun t =>
    div_le_div_of_nonneg_right
      (maximinShare_le_truncatedShare (v t) (hv t) hn) (by positivity))

/-- The same online policy can guarantee the corresponding fraction of MMS. -/
theorem general_mms_guarantee {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => maximinShare (v t) n hn / (2 * (bucketMultiplier k : ℝ)))
        Finset.univ := by
  obtain ⟨policy, hp⟩ := (general_algorithm1_certified hn hk v hv).1
  exact ⟨policy, algorithm1_mms_of_follows hn hk v hv policy hp⟩

end OnlineMMS
