import OnlineMMS.RationalAlgorithm1Cost
import OnlineMMS.BucketRunningScores
import OnlineMMS.BucketTrimScan
import OnlineMMS.RationalTPSSweep

namespace OnlineMMS.RationalAlgorithm1

open BucketBitComplexity
open private initial initialWithTPS smallQ sampleQ widthQ qCoeff cCoeff eligible policyFrom fullBlocks
  from OnlineMMS.RationalAlgorithm1

-- Pass the shared sorted list to the row builder, so each row consumes
-- the already computed order.
@[noinline] private def trimmedRows {m k : ℕ} (R : Finset (Fin m))
    (ordered : List (Fin m)) (w : Fin k → Fin m → ℚ) (cap : ℚ) :
    Vector (Vector ℚ m) k :=
  Vector.ofFn (fun t => trimWeightsOrdered R ordered (w t) cap)

private def fastSmall {m k : ℕ} (r : ℕ) (x : State m k) (R : Finset (Fin m)) : State m k :=
  let ordered := R.sort (· ≤ ·)
  let rows := trimmedRows R ordered x.weight (r + (x.sampleCount : ℚ))
  ⟨R, x.sampleCount, fun t g => (rows.get t).get g, x.products⟩

private theorem fastSmall_eq {m k : ℕ} (r : ℕ) (x : State m k) (B : Finset (Fin m)) :
    fastSmall r x (x.remaining \ B) = smallQ r x B := by
  unfold fastSmall smallQ
  dsimp only
  congr 1
  funext t g
  have hv : (trimmedRows (x.remaining \ B) ((x.remaining \ B).sort (· ≤ ·))
      x.weight (r + (x.sampleCount : ℚ))).get t =
      trimWeightsVector (x.remaining \ B) (x.weight t) (r + (x.sampleCount : ℚ)) := by
    simp [trimmedRows, Vector.get, trimWeightsVector]
  rw [materializeTable_apply, hv, trimWeightsVector_get]

private theorem erase_eq_sdiff {α : Type*} [DecidableEq α] (R : Finset α) (g : α) :
    R.erase g = R \ {g} := by ext x; simp [and_comm]

/-- Length-carrying block splitter. The proof of no duplicates lets it build
a finset without performing a duplicate-removal scan. -/
private def scanBlocks {m : ℕ} (width : ℕ) :
    ℕ → (goods : List (Fin m)) → (count : ℕ) → goods.length = count →
      goods.Nodup → List (Finset (Fin m))
  | 0, _, _, _, _ => []
  | fuel + 1, goods, count, hcount, hn =>
    if count < width then []
    else
      ⟨goods.take width, (List.take_sublist _ _).nodup hn⟩ ::
        scanBlocks width fuel (goods.drop width) (count - width)
          (by simp [List.length_drop, hcount]) ((List.drop_sublist _ _).nodup hn)

private theorem scanBlocks_eq {m : ℕ} (width fuel : ℕ) (goods : List (Fin m))
    (count : ℕ) (hcount : goods.length = count) (hn : goods.Nodup) :
    scanBlocks width fuel goods count hcount hn = fullBlocks width fuel goods := by
  induction fuel generalizing goods count with
  | zero => rfl
  | succ fuel ih =>
    subst count
    simp only [scanBlocks, fullBlocks]
    split
    · rfl
    · congr 1
      · ext g
        simp
      · apply ih

private def fastBuckets {m : ℕ} (w : Fin m → ℚ) (width : ℕ) (R : Finset (Fin m)) :
    List (Finset (Fin m)) :=
  let byIndex := R.sort (· ≤ ·)
  let goods := byIndex.mergeSort (fun g x => decide (w x ≤ w g))
  scanBlocks width R.card goods R.card (by simp [goods, byIndex])
    ((List.mergeSort_perm _ _).nodup_iff.mpr (R.sort_nodup _))

private theorem fastBuckets_eq {m : ℕ} (w : Fin m → ℚ) (width : ℕ) (R : Finset (Fin m)) :
    fastBuckets w width R = rationalBuckets w width R := by
  simp [fastBuckets, rationalBuckets, scanBlocks_eq]

private def markGoods {m : ℕ} : List (Fin m) → Vector Bool m → Vector Bool m
  | [], marked => marked
  | g :: goods, marked => markGoods goods (marked.set g.val true g.isLt)

private theorem markGoods_get {m : ℕ} (goods : List (Fin m)) (marked : Vector Bool m)
    (g : Fin m) : (markGoods goods marked).get g = (decide (g ∈ goods) || marked.get g) := by
  induction goods generalizing marked with
  | nil => simp [markGoods]
  | cons a goods ih =>
    rw [markGoods, ih]
    by_cases ha : g = a
    · subst a
      simp [Vector.get]
    · have hne : a.val ≠ g.val := fun h => ha (Fin.ext h.symm)
      simp [Vector.get, ha, hne, eq_comm]

private def sampleFast {m k : ℕ} (h : ℕ) (x : State m k) (gs : List (Fin m)) :
    Finset (Fin m) × State m k :=
  let marked := markGoods gs (Vector.replicate m false)
  (x.remaining.filter (fun g => marked.get g),
    ⟨x.remaining.filter (fun g => ¬ marked.get g), x.sampleCount + 1, x.weight,
      materialize (fun t => x.products t * sampleProductQ h (gs.map (x.weight t)))⟩)

private theorem sampleFast_eq {m k : ℕ} (h : ℕ) (x : State m k) (gs : List (Fin m))
    (hsub : gs.toFinset ⊆ x.remaining) :
    sampleFast h x gs = (gs.toFinset, sampleQ h x gs) := by
  have hm (g : Fin m) : (markGoods gs (Vector.replicate m false)).get g = decide (g ∈ gs) := by
    rw [markGoods_get]
    simp [Vector.get]
  unfold sampleFast sampleQ
  dsimp only
  congr 1
  · ext g
    simp [hm]
    exact fun hg => hsub (List.mem_toFinset.mpr hg)
  · congr 1
    ext g
    simp [hm]

/-- Algorithm 1 with one traversal for each trimmed row and running
conditional sums and products during a sample. -/
def advanceFast {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k) :
    Finset (Fin m) × State m k :=
  if r = 0 then (x.remaining, {x with remaining := ∅})
  else if 0 < d t then
    let goods := eligible h x t
    if hn : goods.Nonempty then
      let bundle := {goods.min' hn}
      (bundle, fastSmall r x (x.remaining.erase (goods.min' hn)))
    else
      let buckets := fastBuckets (x.weight t) (widthQ h b r x) x.remaining
      let gs := selectLinearQ x.weight h (qCoeff x) (cCoeff h x) x.products [] buckets
      sampleFast h x gs
  else (∅, fastSmall r x x.remaining)

theorem advanceFast_eq {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) (r : ℕ) (x : State m k) (t : Fin k)
    (hx : ∀ i g, 0 ≤ x.weight i g) :
    advanceFast h b d r x t = advance h b d r x t := by
  by_cases hr : r = 0
  · simp [advanceFast, advance, hr]
  by_cases ht : 0 < d t
  · simp only [advanceFast, advance, if_neg hr, if_pos ht, erase_eq_sdiff, fastSmall_eq, fastBuckets_eq]
    by_cases hne : (eligible h x t).Nonempty
    · simp [hne]
    · rw [dif_neg hne, dif_neg hne]
      let H := widthQ h b r x
      let bs := rationalBuckets (x.weight t) H x.remaining
      have hp : 0 < H := by unfold H widthQ; split <;> exact Nat.mul_pos (by assumption) (by omega)
      have hs := rationalBuckets_spec (x.weight t) hp x.remaining
      have hbs (B : Finset (Fin m)) (hB : B ∈ bs) : B.Nonempty :=
        Finset.card_pos.mp (hs.bucket_size B hB ▸ hp)
      rw [selectLinearQ_eq _ _ _ _ _ (by exact_mod_cast (show 1 ≤ h by omega)) hx _ _ hbs]
      have hgreedy := selectQ_greedy x.weight h (qCoeff x) (cCoeff h x) x.products bs hbs []
      exact sampleFast_eq _ _ _ (hs.selected_valid
        (greedy_sample_le_mean _ _ _ _ _ _ _ hgreedy).1).1
  · simp only [advanceFast, advance, if_neg hr, if_neg ht]
    rw [← (show x.remaining \ ∅ = x.remaining from Finset.sdiff_empty), fastSmall_eq]

private def policyFromFast {m k : ℕ} (h b : ℕ) (d : Fin k → ℚ) :
    (n : ℕ) → State m k → Policy m k n
  | 0, _ => .done
  | r + 1, x => .step (fun t => (advanceFast h b d r x t).1)
      (fun t => policyFromFast h b d r (advanceFast h b d r x t).2)

private theorem policyFromFast_eq {m k h b : ℕ} (hh : 0 < h) (hb : 0 < b)
    (d : Fin k → ℚ) {D : Fin k → ℕ} (hD : ∀ i, 0 < D i)
    (n : ℕ) (x : State m k) (hx : GridHistory h D x) :
    policyFromFast h b d n x = policyFrom h b d n x := by
  induction n generalizing x with
  | zero => rfl
  | succ r ih =>
    unfold policyFromFast policyFrom
    have he (t : Fin k) := advanceFast_eq hh hb d r x t (fun i g => (hx.weights i g).2.1)
    congr 1
    · funext t
      rw [he]
    · funext t
      rw [he]
      exact ih _ (advance_gridHistory hh hb d hD r hx t)

/-- The running-sum variant uses the sorted one-pass TPS computation. -/
def fastPolicy {m n k : ℕ} (v : Fin k → Fin m → ℚ) : Policy m k n :=
  let h := parameterQ k
  let d := materialize (fun t => rationalTPSFast (v t) n)
  policyFromFast h (h / 4) d n (initialWithTPS v d)

theorem fastPolicy_eq {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    fastPolicy (n := n) v = policy (n := n) v := by
  obtain ⟨D, hD, hi⟩ := initial_gridHistory (h := parameterQ k) v hv hn
  have hh : 216 ≤ parameterQ k := by rw [parameterQ_eq]; exact (bucketMultiplier_bounds hk).1
  have he : (fun t => rationalTPSFast (v t) n) = fun t => rationalTPS (v t) n :=
    funext (fun t => rationalTPSFast_eq hn (v t) (hv t))
  unfold fastPolicy
  dsimp only
  rw [he]
  exact policyFromFast_eq (by omega) (by omega) _ (fun t => (hD t).1) n _ hi

theorem fastPolicy_guarantees_tps {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) :
    (fastPolicy (n := n) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => truncatedShare (fun g => (v t g : ℝ)) n / (2 * (bucketMultiplier k : ℝ)))
      Finset.univ := by
  rw [fastPolicy_eq hn hk v hv]
  exact policy_guarantees_tps hn hk v hv

end OnlineMMS.RationalAlgorithm1
