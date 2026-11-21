import OnlineMMS.ObliviousLowerSample

namespace OnlineMMS.FirstSample
open ObliviousFixed
noncomputable section

/-- The sample contains exactly one good for every complete bucket. -/
theorem full_bucket_sample_size {G : Type} [DecidableEq G] {w : G → ℝ} {H : ℕ}
    {R : Finset G} {B : List (Finset G)} {gs : List G} (hH : 0 < H)
    (buckets : SortedBuckets w H R B) (selects : List.Forall₂ (fun b g => g ∈ b) B gs) :
    gs.toFinset.card = R.card / H := by
  have count : B.length = R.card / H := by
    clear selects
    induction buckets with
    | tail short => simp [Nat.div_eq_of_lt short]
    | full size disjoint order tail ih =>
      rw [Finset.card_union_of_disjoint disjoint, size, Nat.add_div_left _ hH,
        List.length_cons, ih]
  rw [List.toFinset_card_of_nodup (buckets.selected_valid selects).2, ← selects.length_eq, count]

/-- If every single good is below the target and the reserve pays for two widths,
strictly more than `2H` goods remain. This applies both at `H=hN` and at `H=bN`. -/
theorem sampling_has_two_full_widths {G : Type} {R : Finset G} {H : ℕ} {β : ℝ} (hH : 0 < H)
    (hβ : 0 < β) (w : G → ℝ) (small : ∀ g ∈ R, w g < β)
    (reserve : 2*(H:ℝ)*β ≤ ∑ g ∈ R, w g) : 2*H < R.card := by
  have positive : 0 < 2*(H:ℝ)*β := by positivity
  have ne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    rintro rfl
    simp at reserve
    linarith)
  have lt := Finset.sum_lt_sum_of_nonempty ne small
  have upper : 2*(H:ℝ)*β < R.card*β := reserve.trans_lt (by simpa [nsmul_eq_mul] using lt)
  have result := (mul_lt_mul_right hβ).mp upper
  exact_mod_cast result

/-- The complete degree-two Bonferroni display for weights in `[0,1]`. -/
theorem complement_product_bounds (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    0 ≤ (xs.map (fun x => 1-x)).prod ∧
      (xs.map (fun x => 1-x)).prod ≤ 1-xs.sum+pairSum xs := by
  induction xs with
  | nil => norm_num [pairSum]
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1 := fun x h => hx x (List.mem_cons_of_mem a h)
    have bounds := ih ht
    have hp := pairSum_nonneg xs (fun x h => (ht x h).1)
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pairSum]
    refine ⟨mul_nonneg (sub_nonneg.mpr ha.2) bounds.1,
      (mul_le_mul_of_nonneg_left bounds.2 (sub_nonneg.mpr ha.2)).trans ?_⟩
    nlinarith [mul_nonneg ha.1 hp]

def probability {α : Type} (D : Law α) (A : α → Prop) : ℝ :=
  D.mean (fun a => @ite ℝ (A a) (Classical.propDecidable _) 1 0)

/-- On every draw from disjoint full buckets, the loss summed over positions is the
manuscript's weight of the allocated bundle as a set of goods. -/
theorem bundle_loss_event {m k H : ℕ} {R : Finset (Fin m)} {B : List (Finset (Fin m))}
    (sort : Fin m → ℝ) (buckets : SortedBuckets sort H R B) (hn : ∀ C ∈ B, C.Nonempty)
    (w : Fin k → Fin m → ℝ) (K : Finset (Fin k)) (threshold : ℝ) :
    probability (drawBuckets B hn) (fun gs => ∃ t ∈ K, threshold < (gs.map (w t)).sum) =
      probability (drawBuckets B hn) (fun gs => ∃ t ∈ K, threshold < bundleValue (w t) gs.toFinset) := by
  unfold probability
  apply Law.mean_congr
  intro i
  have nodup := (buckets.selected_valid (drawBuckets_selection B hn i)).2
  simp only [FixedWidth.weight_list_sum _ _ nodup]
  by_cases h : ∃ t ∈ K, threshold < bundleValue (w t) ((drawBuckets B hn).val i).toFinset <;> simp [h]

private theorem markov {α : Type} (D : Law α) (A : α → Prop) (f : α → ℝ) {c : ℝ}
    (hc : 0 < c) (hn : ∀ a, 0 ≤ f a) (ha : ∀ a, A a → c ≤ f a) :
    probability D A ≤ D.mean f / c := by
  classical
  apply (le_div_iff₀ hc).mpr
  rw [mul_comm, probability, ← Law.mean_smul]
  apply Law.mean_mono
  intro i
  by_cases h : A (D.val i)
  · simpa [h] using ha _ h
  · simpa [h] using hn (D.val i)

private theorem union_bound {α I : Type} (D : Law α) (K : Finset I) (A : I → α → Prop) :
    probability D (fun a => ∃ t ∈ K, A t a) ≤ ∑ t ∈ K, probability D (A t) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp [probability]
  | @insert t K ht ih =>
    rw [Finset.sum_insert ht]
    refine le_trans ?_ (add_le_add_left ih _)
    unfold probability
    rw [← Law.mean_add]
    apply Law.mean_mono
    intro i
    by_cases h1 : A t (D.val i) <;> by_cases h2 : ∃ s ∈ K, A s (D.val i) <;> simp [h1,h2]

/-- Under independent bucket draws, both the expected loss and the expected sum of
unordered weight products equal their values on the bucket means. -/
theorem pair_expectation {k : ℕ} {G : Type} (w : Fin k → G → ℝ) (t : Fin k)
    (B : List (Finset G)) (hn : ∀ b ∈ B, b.Nonempty) :
    let D := drawBuckets B hn
    let row := (slotMeans w B).map (fun a => a t)
    D.mean (fun gs => (gs.map (w t)).sum) = row.sum ∧
      D.mean (fun gs => pairSum (gs.map (w t))) = pairSum row := by
  induction B with
  | nil => simp [drawBuckets, slotMeans, pairSum]
  | cons C rest ih =>
    have hr : ∀ b ∈ rest, b.Nonempty := fun b hb => hn b (by simp [hb])
    obtain ⟨hS,hP⟩ := ih hr
    let Z := ((slotMeans w rest).map (fun a => a t)).sum
    let Q := pairSum ((slotMeans w rest).map (fun a => a t))
    constructor
    · change ((draw C _).bind _).mean _ = (slotMean w C t)+Z
      rw [Law.mean_bind]
      simp only [Law.mean_map, List.map_cons, List.sum_cons]
      simp_rw [Law.mean_add, Law.mean_const, hS]
      rw [mean_draw]
      rfl
    · change ((draw C _).bind _).mean _ = (slotMean w C t)*Z+Q
      rw [Law.mean_bind]
      simp only [Law.mean_map, List.map_cons, pairSum]
      simp_rw [Law.mean_add, Law.mean_smul, hS, hP]
      rw [Law.mean_const]
      change (draw C _).mean (fun g => w t g * Z) + Q = _
      congr 1
      calc
        _ = (draw C _).mean (fun g => Z * w t g) := by
          apply Law.mean_congr
          intro _
          exact mul_comm _ _
        _ = _ := by rw [Law.mean_smul, mean_draw]; exact mul_comm _ _

/-- Both Markov bounds for the actual independent uniform bucket draw. The conclusions
hold for each protected type and for the event that at least one protected type suffers
excessive loss. The union bounds even retain the exact number of protected types. -/
theorem first_sample_probability_bounds {k : ℕ} {G : Type} [DecidableEq G]
    (w : Fin k → G → ℝ) (K : Finset (Fin k)) (R : Finset G) (B : List (Finset G))
    {h N : ℕ} (hh : 1 ≤ h) (hN : 0 < N) (sort : G → ℝ)
    (buckets : SortedBuckets sort (h*N) R B)
    (hn : ∀ C ∈ B, C.Nonempty)
    (weights : ∀ t g, 0 ≤ w t g ∧ w t g ≤ 1)
    (cap : ∀ t ∈ K, (∑ g ∈ R, w t g) ≤ (N : ℝ)) :
    let β := 1/(2*(h:ℝ))
    let D := drawBuckets B hn
    let bad := fun (t : Fin k) (gs : List G) => 2-β < (gs.map (w t)).sum
    let pairBound := 1/(2*(1-β)*(h:ℝ)^2)
    let productBound := Real.exp (1-1/(h:ℝ)) / (h:ℝ)^(2-β)
    (∀ t ∈ K, probability D (bad t) ≤ pairBound ∧ probability D (bad t) ≤ productBound) ∧
      (probability D (fun gs => ∃ t ∈ K, bad t gs) ≤ K.card*pairBound ∧
       probability D (fun gs => ∃ t ∈ K, bad t gs) ≤ K.card*productBound) ∧
      (probability D (fun gs => ∃ t ∈ K, bad t gs) ≤ k*pairBound ∧
       probability D (fun gs => ∃ t ∈ K, bad t gs) ≤ k*productBound) := by
  classical
  let β := 1/(2*(h:ℝ))
  let D := drawBuckets B hn
  let bad (t : Fin k) (gs : List G) := 2-β < (gs.map (w t)).sum
  let pairBound := 1/(2*(1-β)*(h:ℝ)^2)
  let productBound := Real.exp (1-1/(h:ℝ)) / (h:ℝ)^(2-β)
  have h1 : 1 ≤ (h:ℝ) := by exact_mod_cast hh
  have hp : 0 < (h:ℝ) := by linarith
  have np : 0 < (N:ℝ) := by exact_mod_cast hN
  have hβ : 0 < 1-β := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ (by positivity : 0 < 2*(h:ℝ))).mpr (by linarith)
  have hx (t : Fin k) (gs : List G) : ∀ z ∈ gs.map (w t), 0 ≤ z ∧ z ≤ 1 := by
    intro z hz
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hz
    exact weights t g
  have per (t : Fin k) (ht : t ∈ K) :
      probability D (bad t) ≤ pairBound ∧ probability D (bad t) ≤ productBound := by
    let row := (slotMeans w B).map (fun a => a t)
    have hw : row.sum ≤ 1/(h:ℝ) := by
      have z := slotMeans_sum_le_of_width w B R (h*N) buckets.pairwise_disjoint buckets.bucket_size
        buckets.bucket_subsets t (fun g => (weights t g).1)
      refine z.trans ((div_le_div_of_nonneg_right (cap t ht) (Nat.cast_nonneg _)).trans ?_)
      push_cast
      exact le_of_eq (by field_simp; ring)
    have hz := slotMeans_nonneg w B t (fun g => (weights t g).1)
    have hs : 0 ≤ row.sum := List.sum_nonneg hz
    constructor
    · have bound := markov D (bad t) (fun gs => pairSum (gs.map (w t))) hβ
        (fun gs => pairSum_nonneg _ (fun z hz => (hx t gs z hz).1)) (by
          intro gs hb
          change 2-β < _ at hb
          linarith [sum_le_one_add_pairSum _ (hx t gs)])
      rw [(pair_expectation w t B hn).2] at bound
      refine bound.trans ((div_le_div_of_nonneg_right (show pairSum row ≤ (1/(h:ℝ))^2 / 2 by
        nlinarith [twice_pairSum_le_sum_sq row, pow_le_pow_left₀ hs hw 2]) hβ.le).trans ?_)
      dsimp [pairBound]; exact le_of_eq (by field_simp; ring)
    · have bound := markov D (bad t) (fun gs => sampleProduct (h:ℝ) (gs.map (w t)))
        (Real.rpow_pos_of_pos hp (2-β))
        (fun gs => sampleProduct_nonneg h1 _ (fun z hz => (hx t gs z hz).1)) (by
          intro gs hb
          exact (Real.rpow_le_rpow_of_exponent_le h1 (le_of_lt hb)).trans (rpow_sum_le_sampleProduct h1 _ (hx t gs)))
      rw [mean_drawBuckets_product] at bound
      apply bound.trans
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      refine (sampleProduct_le_exp h1 row hz).trans (Real.exp_le_exp.mpr ?_)
      refine (mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ (h:ℝ)-1)).trans_eq ?_
      field_simp
  have union := union_bound D K bad
  have forK (c : ℝ) (hc : ∀ t ∈ K, probability D (bad t) ≤ c) :=
    union.trans ((Finset.sum_le_sum hc).trans_eq (show (∑ _ ∈ K, c) = K.card*c by simp [nsmul_eq_mul]))
  have pairK := forK _ (fun t ht => (per t ht).1)
  have productK := forK _ (fun t ht => (per t ht).2)
  have H : (K.card : ℝ) ≤ k := by exact_mod_cast (show K.card ≤ k by simpa using K.card_le_univ)
  exact ⟨per, ⟨pairK, productK⟩,
    pairK.trans (mul_le_mul_of_nonneg_right H (by dsimp [pairBound]; positivity)),
    productK.trans (mul_le_mul_of_nonneg_right H (by dsimp [productBound]; positivity))⟩

end
end OnlineMMS.FirstSample
