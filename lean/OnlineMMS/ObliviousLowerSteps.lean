import OnlineMMS.ObliviousLowerPolicy
import OnlineMMS.ObliviousLowerSample

namespace OnlineMMS.ObliviousFixed
noncomputable section

open FixedWidth

abbrev BucketState (m k : ℕ) := State m k Unit

def admissible {m k} (v : Fin k → Fin m → ℝ) (d : Fin k → ℝ)
    (r : ℕ) (x : BucketState m k) : Prop := Valid v d r x ∧ (r=0 → x.remaining = ∅)

def potential {m k} (h : ℝ) (d : Fin k → ℝ) (r : ℕ) (x : BucketState m k) (u : Fin k) : ℝ :=
  if 0 < d u then h ^ deficit x r u / (3:ℝ)^x.samples else 0

theorem potential_nonneg {m k} {h : ℝ} (hh : 0 ≤ h) (d : Fin k → ℝ)
    (r : ℕ) (x : BucketState m k) (u : Fin k) : 0 ≤ potential h d r x u := by
  simp only [potential]; split_ifs
  · exact div_nonneg (Real.rpow_nonneg hh _) (by positivity)
  · exact le_rfl

theorem potential_initial {m k n} (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (hn : 0<n) (h : ℝ) (t : Fin k) :
    potential h (fun u => truncatedShare (v u) n) n (init v n ()) t ≤ 1 := by
  have hi := valid_init hn v hv ()
  unfold potential
  split_ifs with ht
  · have hex := hi.exactBefore rfl t ht
    rw [deficit, hex]
    simp [init]
  · norm_num

private theorem value_floor {m k} {v : Fin k → Fin m → ℝ} {d : Fin k → ℝ}
    {β : ℝ} {r : ℕ} {x : BucketState m k} (hx : Valid v d r x)
    (t : Fin k) (ht : 0 ≤ d t) {B : Finset (Fin m)} (hw : β ≤ bundleValue (x.weight t) B) :
    d t * β ≤ bundleValue (v t) B := by
  calc
    _ ≤ d t * bundleValue (x.weight t) B := mul_le_mul_of_nonneg_left hw ht
    _ = ∑ g ∈ B, d t * x.weight t g := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun g _ => hx.value t g)

private def stopped {m k} : BucketState m k := ⟨∅, 0, fun _ _ => 0, ()⟩

private theorem stopped_valid {m k} (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (d : Fin k → ℝ) : admissible v d 0 (stopped : BucketState m k) := by
  refine ⟨⟨fun _ _ => by simp [stopped], fun t g => by simpa [stopped] using hv t g, ?_, ?_⟩, fun _ => rfl⟩
  · simp [total, stopped, bundleValue]
  · simp [total, stopped, bundleValue]

private theorem small_law {m k r} {v : Fin k → Fin m → ℝ} {d : Fin k → ℝ}
    {x : BucketState m k} (hx : admissible v d (r+1) x) (hr : r ≠ 0)
    (hd : ∀ t, 0 ≤ d t) {h : ℝ} (hh : 1 ≤ h)
    {t : Fin k} {B : Finset (Fin m)} (hsub : B ⊆ x.remaining)
    (hB : ∀ u, bundleValue (x.weight u) B ≤ 1)
    {floor : Fin k → ℝ} (hp : floor t ≤ bundleValue (v t) B)
    (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a) :
    ∃ D : Law (Move State.remaining (admissible v d) r x),
      D.All (fun a => miss (floor t) (bundleValue (v t) a.bundle) ≤ q (r+1)*potential h d (r+1) x t)
      ∧ (r ≠ 0 → ∀ u, D.mean (fun a => potential h d r a.next u) ≤ potential h d (r+1) x u) := by
  have hs := small_valid hx.1 hd hsub hB
  let a : Move State.remaining (admissible v d) r x :=
    ⟨B, afterSmall r x B, hsub, rfl, hs.1, fun h0 => (hr h0).elim⟩
  refine ⟨Law.pure a, ?_, ?_⟩
  · intro _
    change miss (floor t) (bundleValue (v t) B) ≤ _
    rw [miss, if_pos hp]
    exact mul_nonneg (hq _) (potential_nonneg (by linarith) ..)
  · intro _ u
    rw [Law.mean_pure]
    unfold potential
    split_ifs
    · exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hh (hs.2 u)) (by positivity)
    · exact le_rfl

/-- Any numerical charges satisfying the two shortage estimates are enough
for the one-width sampling rule. The validity predicate is preserved even on a path
where some arriving agent has already missed her target. -/
theorem bucket_step {m k h : ℕ} (hh : 16 ≤ h)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g)
    (d floor : Fin k → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hfloor : ∀ t, floor t ≤ d t * (1 / (8*(h:ℝ))))
    (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a)
    (qLast : ∀ (s : ℕ) (W : ℝ), 0<s → W < 1/(8*(h:ℝ)) →
      1 ≤ q 1 * ((h:ℝ)^((1:ℝ)+s-W)/(3:ℝ)^s))
    (qEarlier : ∀ (r s : ℕ) (W : ℝ), 2≤r → 0<s → W < ((r:ℝ)+s)/4 →
      1 ≤ q r * ((h:ℝ)^((r:ℝ)+s-W)/(3:ℝ)^s))
    (r : ℕ) (x : BucketState m k) (hx : admissible v d (r+1) x) (t : Fin k) :
    ∃ D : Law (Move State.remaining (admissible v d) r x),
      D.All (fun a => miss (floor t) (bundleValue (v t) a.bundle) ≤ q (r+1)*potential h d (r+1) x t)
      ∧ (r ≠ 0 → ∀ u, D.mean (fun a => potential h d r a.next u) ≤ potential h d (r+1) x u) := by
  classical
  let β : ℝ := 1/(8*(h:ℝ))
  have h16 : (16:ℝ) ≤ h := by exact_mod_cast hh
  have hR : 0 < (h:ℝ) := by linarith
  have h1 : 1 ≤ (h:ℝ) := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := (div_le_one₀ (by positivity : 0<8*(h:ℝ))).mpr (by linarith)
  have budget0 : 0 ≤ q (r+1)*potential h d (r+1) x t := mul_nonneg (hq _) (potential_nonneg hR.le ..)
  by_cases hr : r=0
  · subst r
    let a : Move State.remaining (admissible v d) 0 x :=
      ⟨x.remaining, stopped, Finset.Subset.rfl, by simp [stopped], stopped_valid v hv d⟩
    refine ⟨Law.pure a, ?_, fun hn => (hn rfl).elim⟩
    intro _
    change miss (floor t) (bundleValue (v t) x.remaining) ≤ _
    by_cases paid : floor t ≤ bundleValue (v t) x.remaining
    · simpa [miss, paid] using budget0
    · rw [miss, if_neg paid]
      have ht : 0 < d t := by
        by_contra! hz
        have hd0 : d t = 0 := le_antisymm hz (hd t)
        have nonneg : 0 ≤ bundleValue (v t) x.remaining := Finset.sum_nonneg fun g _ => hv t g
        exact paid ((hfloor t).trans (by simpa [hd0] using nonneg))
      have hW : total x t < β := lt_of_not_ge (fun hW => paid ((hfloor t).trans
        (value_floor hx.1 t (hd t) hW)))
      have hs : 0 < x.samples := by
        by_contra! hz
        have he := hx.1.exactBefore (by omega) t ht
        norm_num at he
        linarith
      simpa [potential, ht, deficit] using qLast x.samples (total x t) hs hW
  by_cases ht : 0 < d t
  · by_cases single : ∃ g ∈ x.remaining, β ≤ x.weight t g
    · obtain ⟨g,hg,hpay⟩ := single
      exact small_law hx hr hd h1 (Finset.singleton_subset_iff.mpr hg)
        (fun u => by simpa [bundleValue] using (hx.1.weights u g).2)
        ((hfloor t).trans (value_floor (β := β) hx.1 t ht.le (by simpa [bundleValue] using hpay))) q hq
    · let H := h * (r+1+x.samples)
      have hH : 0<H := Nat.mul_pos (by omega) (by omega)
      obtain ⟨b,hb⟩ := SortedBuckets.exists_buckets (w := x.weight t) hH x.remaining
      have hne (C : Finset (Fin m)) (hc : C ∈ b) : C.Nonempty := Finset.card_pos.mp (hb.bucket_size C hc ▸ hH)
      let picks := drawBuckets b hne
      have hsel := drawBuckets_selection b hne
      have nextOk (i : picks.Atom) :=
        let gs := picks.val i
        let sel := hb.selected_valid (hsel i)
        sample_valid hx.1 sel.1 sel.2 ()
      let move (i : picks.Atom) : Move State.remaining (admissible v d) r x :=
        ⟨(picks.val i).toFinset, afterSample x (picks.val i) (),
          (hb.selected_valid (hsel i)).1, rfl, (nextOk i).1, fun h0 => (hr h0).elim⟩
      let D : Law (Move State.remaining (admissible v d) r x) :=
        ⟨picks.Atom, picks.finite, picks.mass, picks.nonneg, picks.total, move⟩
      refine ⟨D, ?_, ?_⟩
      · intro i
        let gs := picks.val i
        change miss (floor t) (bundleValue (v t) gs.toFinset) ≤ _
        by_cases paid : floor t ≤ bundleValue (v t) gs.toFinset
        · simpa [miss, paid] using budget0
        · rw [miss, if_neg paid]
          have hloss : (gs.map (x.weight t)).sum < β := by
            apply lt_of_not_ge
            intro hw
            rw [weight_list_sum _ _ (hb.selected_valid (hsel i)).2] at hw
            exact paid ((hfloor t).trans (value_floor hx.1 t ht.le hw))
          have hsorted := hb.payment (hsel i) (fun g => (hx.1.weights t g).1) hβ
            (fun g hg => le_of_lt (lt_of_not_ge (fun h => single ⟨g,hg,h⟩)))
          have hsmall : total x t < ((((r+1:ℕ):ℝ)+x.samples)/4) := by
            have hhpos : (0:ℝ)<H := by exact_mod_cast hH
            have strict := mul_lt_mul_of_pos_left (add_lt_add_left hloss β) hhpos
            have hscale : (H:ℝ)*(β+β) = (((r+1:ℕ):ℝ)+x.samples)/4 := by
              dsimp [H,β]; push_cast; field_simp; ring
            exact (lt_of_le_of_lt hsorted strict).trans_le hscale.le
          have hs : 0 < x.samples := by
            apply Nat.pos_of_ne_zero
            intro hs0
            rw [hx.1.exactBefore hs0 t ht, hs0] at hsmall
            push_cast at hsmall
            linarith [Nat.cast_nonneg (α := ℝ) r]
          simpa [potential, ht, deficit] using qEarlier (r+1) x.samples (total x t) (by omega) hs hsmall
      · intro _ u
        by_cases hu : 0 < d u
        · let A := (h:ℝ)^deficit x (r+1) u / (3:ℝ)^(x.samples+1)
          have hA : 0 ≤ A := div_nonneg (Real.rpow_nonneg hR.le _) (by positivity)
          have one (i : picks.Atom) :
              potential h d r (move i).next u ≤ A * sampleProduct h ((picks.val i).map (x.weight u)) := by
            let gs := picks.val i
            have hs := (nextOk i).2 u
            have hxs : ∀ z ∈ gs.map (x.weight u), 0 ≤ z ∧ z ≤ 1 := by
              intro z hz
              obtain ⟨g,_,rfl⟩ := List.mem_map.mp hz
              exact hx.1.weights u g
            have hprod := rpow_deficit_add_le (D := deficit x (r+1) u) h1 _ hxs le_rfl
            unfold potential
            rw [if_pos hu]
            change (h:ℝ) ^ deficit (afterSample x gs ()) r u / (3:ℝ)^(x.samples+1) ≤ _
            rw [hs]
            exact (div_le_div_of_nonneg_right hprod (by positivity)).trans_eq (by dsimp [A,gs]; ring)
          have hmean := sample_exp_mean_bound hh hx.1 t u b hb hne
          calc
            _ ≤ ∑ i : picks.Atom, picks.mass i * (A * sampleProduct h ((picks.val i).map (x.weight u))) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (one i) (picks.nonneg i)
            _ = A * picks.mean (fun gs => sampleProduct h (gs.map (x.weight u))) := by
              unfold Law.mean; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
            _ ≤ A*3 := mul_le_mul_of_nonneg_left hmean hA
            _ = _ := by unfold potential; rw [if_pos hu]; dsimp [A]; rw [pow_succ]; ring
        · simp only [potential, if_neg hu, Law.mean_const, le_refl]
  · have hd0 : d t=0 := le_antisymm (le_of_not_gt ht) (hd t)
    exact small_law hx hr hd h1 (Finset.empty_subset _) (fun u => by simp [bundleValue])
      ((hfloor t).trans (by simp [hd0, bundleValue])) q hq

end
end OnlineMMS.ObliviousFixed
